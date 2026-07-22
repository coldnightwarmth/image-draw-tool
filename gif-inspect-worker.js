import { decompressFrame, parseGIF } from "./gifuct-js.bundle.mjs";

// Create this worker with `{ type: "module" }`.
//
// Protocol v1 requests:
//   { protocol: "gif-inspect", version: 1, type: "inspect", jobId,
//     source: { url } | { buffer }, options? }
//   { protocol: "gif-inspect", version: 1, type: "cancel", jobId }
//
// Every terminal response repeats protocol, version, type, and jobId. Inspect
// requests finish with `result`, `error`, or `cancelled`. Structured errors
// include stable `code` and `category` fields so callers can keep hard safety
// failures terminal while choosing a bounded fallback for capability failures.
// A cancel for a job that is no longer active gets an immediate `cancelled`
// response with `active: false`.

export const GIF_INSPECT_PROTOCOL = "gif-inspect";
export const GIF_INSPECT_VERSION = 1;

const DEFAULT_FRAME_DELAY_MS = 100;
const DEFAULT_MAX_INPUT_BYTES = 128 * 1024 * 1024;
const DEFAULT_MAX_OPACITY_PIXELS = 16 * 1024 * 1024;
const MAX_CONFIGURABLE_INPUT_BYTES = 512 * 1024 * 1024;
const MAX_CONFIGURABLE_OPACITY_PIXELS = 64 * 1024 * 1024;
const OPACITY_YIELD_INTERVAL = 4;

class GifInspectError extends Error {
  constructor(
    code,
    message,
    { category = "input", retriable = false, details = null } = {}
  ) {
    super(message);
    this.name = "GifInspectError";
    this.code = code;
    this.category = category;
    this.retriable = retriable;
    this.details = details;
  }
}

function clampInteger(value, fallback, minimum, maximum) {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) {
    return fallback;
  }
  return Math.min(maximum, Math.max(minimum, Math.floor(numeric)));
}

function normalizeOptions(options) {
  const raw = options && typeof options === "object" ? options : {};
  return {
    checkOpacity: raw.checkOpacity !== false,
    maxInputBytes: clampInteger(
      raw.maxInputBytes,
      DEFAULT_MAX_INPUT_BYTES,
      1,
      MAX_CONFIGURABLE_INPUT_BYTES
    ),
    maxOpacityPixels: clampInteger(
      raw.maxOpacityPixels,
      DEFAULT_MAX_OPACITY_PIXELS,
      1,
      MAX_CONFIGURABLE_OPACITY_PIXELS
    ),
  };
}

function throwIfCancelled(signal) {
  if (signal?.aborted) {
    throw new DOMException("GIF inspection was cancelled.", "AbortError");
  }
}

function yieldToWorker() {
  return new Promise((resolve) => setTimeout(resolve, 0));
}

function normalizeArrayBuffer(value) {
  if (value instanceof ArrayBuffer) {
    return value;
  }
  if (ArrayBuffer.isView(value)) {
    return value.buffer.slice(value.byteOffset, value.byteOffset + value.byteLength);
  }
  throw new GifInspectError(
    "INVALID_SOURCE",
    "The GIF source must contain either a URL or an ArrayBuffer."
  );
}

function validateGifBytes(arrayBuffer, maxInputBytes) {
  if (arrayBuffer.byteLength > maxInputBytes) {
    throw new GifInspectError("INPUT_TOO_LARGE", "The GIF exceeds the configured byte limit.", {
      category: "safety",
      details: { byteLength: arrayBuffer.byteLength, maxInputBytes },
    });
  }
  if (arrayBuffer.byteLength < 13) {
    throw new GifInspectError("INVALID_GIF", "The source is too short to be a valid GIF.");
  }
  const bytes = new Uint8Array(arrayBuffer, 0, 6);
  const signature = String.fromCharCode(...bytes);
  if (signature !== "GIF87a" && signature !== "GIF89a") {
    throw new GifInspectError("INVALID_GIF", "The source does not have a valid GIF signature.");
  }
}

function normalizeFrameDelayMs(frame) {
  const centiseconds = Number(frame?.gce?.delay);
  return Number.isFinite(centiseconds) && centiseconds > 0
    ? Math.round(centiseconds * 10)
    : DEFAULT_FRAME_DELAY_MS;
}

function getFrameBounds(frame) {
  const descriptor = frame?.image?.descriptor || {};
  return {
    left: Math.trunc(Number(descriptor.left) || 0),
    top: Math.trunc(Number(descriptor.top) || 0),
    width: Math.max(0, Math.trunc(Number(descriptor.width) || 0)),
    height: Math.max(0, Math.trunc(Number(descriptor.height) || 0)),
  };
}

function frameCoversCanvas(frame, width, height) {
  const bounds = getFrameBounds(frame);
  return (
    bounds.width > 0 &&
    bounds.height > 0 &&
    bounds.left <= 0 &&
    bounds.top <= 0 &&
    bounds.left + bounds.width >= width &&
    bounds.top + bounds.height >= height
  );
}

function frameDeclaresTransparency(frame) {
  return frame?.gce?.extras?.transparentColorGiven === true;
}

function makeOpacityResult(value, method, inspectedFrames, reason) {
  return {
    value,
    status: value === true ? "opaque" : value === false ? "not-opaque" : "unknown",
    method,
    inspectedFrames,
    reason,
  };
}

function getClippedFrameRect(bounds, width, height) {
  const left = Math.max(0, bounds.left);
  const top = Math.max(0, bounds.top);
  const right = Math.min(width, bounds.left + bounds.width);
  const bottom = Math.min(height, bounds.top + bounds.height);
  return {
    left,
    top,
    right,
    bottom,
    width: Math.max(0, right - left),
    height: Math.max(0, bottom - top),
  };
}

function applyFrameToOpacityMask(mask, opaqueCount, decoded, canvasWidth, canvasHeight) {
  const bounds = {
    left: Math.trunc(Number(decoded?.dims?.left) || 0),
    top: Math.trunc(Number(decoded?.dims?.top) || 0),
    width: Math.max(0, Math.trunc(Number(decoded?.dims?.width) || 0)),
    height: Math.max(0, Math.trunc(Number(decoded?.dims?.height) || 0)),
  };
  const clipped = getClippedFrameRect(bounds, canvasWidth, canvasHeight);
  const pixels = decoded?.pixels;
  if (!pixels || pixels.length < bounds.width * bounds.height) {
    throw new GifInspectError("FRAME_DECODE_FAILED", "A GIF frame decoded incompletely.");
  }

  const hasTransparency = Number.isInteger(decoded.transparentIndex);
  const transparentIndex = hasTransparency ? decoded.transparentIndex : -1;
  const localStartX = clipped.left - bounds.left;
  const localEndX = localStartX + clipped.width;
  const localStartY = clipped.top - bounds.top;
  const localEndY = localStartY + clipped.height;

  for (let localY = localStartY; localY < localEndY; localY += 1) {
    const sourceRow = localY * bounds.width;
    const targetRow = (bounds.top + localY) * canvasWidth;
    for (let localX = localStartX; localX < localEndX; localX += 1) {
      if (hasTransparency && pixels[sourceRow + localX] === transparentIndex) {
        continue;
      }
      const targetIndex = targetRow + bounds.left + localX;
      if (mask[targetIndex] === 0) {
        mask[targetIndex] = 1;
        opaqueCount += 1;
      }
    }
  }

  return { bounds, opaqueCount };
}

function clearFrameFromOpacityMask(mask, opaqueCount, bounds, canvasWidth, canvasHeight) {
  const clipped = getClippedFrameRect(bounds, canvasWidth, canvasHeight);
  for (let y = clipped.top; y < clipped.bottom; y += 1) {
    const row = y * canvasWidth;
    for (let x = clipped.left; x < clipped.right; x += 1) {
      const index = row + x;
      if (mask[index] !== 0) {
        mask[index] = 0;
        opaqueCount -= 1;
      }
    }
  }
  return opaqueCount;
}

async function inspectConservativeOpacity(
  parsed,
  imageFrames,
  width,
  height,
  maxOpacityPixels,
  signal
) {
  // This structural proof needs no pixel decompression. Each displayed frame
  // overwrites the entire logical canvas with palette entries that cannot be
  // transparent, so disposal state cannot affect the displayed result.
  const structurallyOpaque = imageFrames.every(
    (frame) => !frameDeclaresTransparency(frame) && frameCoversCanvas(frame, width, height)
  );
  if (structurallyOpaque) {
    return makeOpacityResult(
      true,
      "structural",
      0,
      "Every frame fully covers the canvas and declares no transparent color."
    );
  }

  const pixelCount = width * height;
  if (!Number.isSafeInteger(pixelCount) || pixelCount > maxOpacityPixels) {
    return makeOpacityResult(
      null,
      "bounded",
      0,
      "The logical canvas exceeds the configured opacity pixel limit."
    );
  }

  // One byte per logical pixel tracks alpha coverage only. Palette indices are
  // decompressed a frame at a time with buildPatch=false, avoiding RGBA frame
  // patches and avoiding full-frame color compositing.
  let opacityMask = new Uint8Array(pixelCount);
  let opaqueCount = 0;
  let inspectedFrames = 0;

  for (let index = 0; index < imageFrames.length; index += 1) {
    throwIfCancelled(signal);
    const frame = imageFrames[index];
    const disposalType = Number(frame?.gce?.extras?.disposal) || 0;
    const restoreMask = disposalType === 3 ? opacityMask.slice() : null;
    const restoreOpaqueCount = opaqueCount;

    let decoded;
    try {
      decoded = decompressFrame(frame, parsed.gct, false);
    } catch (error) {
      return makeOpacityResult(
        null,
        "alpha-mask",
        inspectedFrames,
        `A frame could not be decompressed: ${error instanceof Error ? error.message : "unknown error"}`
      );
    }
    if (!decoded) {
      return makeOpacityResult(
        null,
        "alpha-mask",
        inspectedFrames,
        "A frame could not be decompressed."
      );
    }

    let applied;
    try {
      applied = applyFrameToOpacityMask(
        opacityMask,
        opaqueCount,
        decoded,
        width,
        height
      );
    } catch (error) {
      return makeOpacityResult(
        null,
        "alpha-mask",
        inspectedFrames,
        error instanceof Error ? error.message : "A frame could not be inspected."
      );
    }
    opaqueCount = applied.opaqueCount;
    inspectedFrames += 1;

    if (opaqueCount !== pixelCount) {
      return makeOpacityResult(
        false,
        "alpha-mask",
        inspectedFrames,
        "At least one displayed frame leaves transparent canvas pixels."
      );
    }

    if (disposalType === 2) {
      opaqueCount = clearFrameFromOpacityMask(
        opacityMask,
        opaqueCount,
        applied.bounds,
        width,
        height
      );
    } else if (disposalType === 3 && restoreMask) {
      opacityMask = restoreMask;
      opaqueCount = restoreOpaqueCount;
    }

    if ((index + 1) % OPACITY_YIELD_INTERVAL === 0) {
      await yieldToWorker();
    }
  }

  return makeOpacityResult(
    true,
    "alpha-mask",
    inspectedFrames,
    "Every displayed frame fully covers the canvas after GIF disposal is applied."
  );
}

export async function inspectGifArrayBuffer(input, rawOptions = {}, signal = null) {
  const options = normalizeOptions(rawOptions);
  const arrayBuffer = normalizeArrayBuffer(input);
  validateGifBytes(arrayBuffer, options.maxInputBytes);
  throwIfCancelled(signal);

  let parsed;
  try {
    parsed = parseGIF(arrayBuffer);
  } catch (error) {
    throw new GifInspectError("PARSE_FAILED", "The GIF could not be parsed.", {
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }
  throwIfCancelled(signal);

  const width = Math.trunc(Number(parsed?.lsd?.width) || 0);
  const height = Math.trunc(Number(parsed?.lsd?.height) || 0);
  if (width <= 0 || height <= 0) {
    throw new GifInspectError("INVALID_DIMENSIONS", "The GIF has invalid logical dimensions.");
  }

  const imageFrames = Array.isArray(parsed?.frames)
    ? parsed.frames.filter((frame) => frame?.image)
    : [];
  if (!imageFrames.length) {
    throw new GifInspectError("NO_FRAMES", "The GIF does not contain any image frames.");
  }

  const frameDelaysMs = imageFrames.map(normalizeFrameDelayMs);
  const totalDurationMs = frameDelaysMs.reduce((total, delay) => total + delay, 0);
  const opacity = options.checkOpacity
    ? await inspectConservativeOpacity(
        parsed,
        imageFrames,
        width,
        height,
        options.maxOpacityPixels,
        signal
      )
    : makeOpacityResult(null, "skipped", 0, "Opacity inspection was disabled.");

  throwIfCancelled(signal);
  return {
    width,
    height,
    frameCount: imageFrames.length,
    frameDelaysMs,
    totalDurationMs,
    animated: imageFrames.length > 1,
    opaque: opacity.value,
    opacity,
    byteLength: arrayBuffer.byteLength,
  };
}

async function readResponseWithLimit(response, maxInputBytes, signal) {
  const declaredLength = Number(response.headers.get("content-length"));
  if (Number.isFinite(declaredLength) && declaredLength > maxInputBytes) {
    throw new GifInspectError("INPUT_TOO_LARGE", "The GIF exceeds the configured byte limit.", {
      category: "safety",
      details: { byteLength: declaredLength, maxInputBytes },
    });
  }

  if (!response.body?.getReader) {
    const buffer = await response.arrayBuffer();
    validateGifBytes(buffer, maxInputBytes);
    return buffer;
  }

  const reader = response.body.getReader();
  const chunks = [];
  let byteLength = 0;
  try {
    while (true) {
      throwIfCancelled(signal);
      const { done, value } = await reader.read();
      if (done) {
        break;
      }
      byteLength += value.byteLength;
      if (byteLength > maxInputBytes) {
        await reader.cancel("GIF input exceeded its byte limit.");
        throw new GifInspectError("INPUT_TOO_LARGE", "The GIF exceeds the configured byte limit.", {
          category: "safety",
          details: { byteLength, maxInputBytes },
        });
      }
      chunks.push(value);
    }
  } finally {
    reader.releaseLock();
  }

  const bytes = new Uint8Array(byteLength);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes.buffer;
}

async function loadSource(source, options, controller) {
  const hasUrl = typeof source?.url === "string" && source.url.trim().length > 0;
  const hasBuffer = source?.buffer instanceof ArrayBuffer || ArrayBuffer.isView(source?.buffer);
  if (hasUrl === hasBuffer) {
    throw new GifInspectError(
      "INVALID_SOURCE",
      "Provide exactly one GIF source: source.url or source.buffer."
    );
  }
  if (hasBuffer) {
    return normalizeArrayBuffer(source.buffer);
  }

  let response;
  try {
    response = await fetch(source.url, {
      signal: controller.signal,
      credentials: "same-origin",
    });
  } catch (error) {
    if (controller.signal.aborted) {
      throw error;
    }
    throw new GifInspectError("FETCH_FAILED", "The GIF URL could not be fetched.", {
      category: "network",
      retriable: true,
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }
  if (!response.ok) {
    throw new GifInspectError("FETCH_FAILED", `The GIF request failed with HTTP ${response.status}.`, {
      category: "network",
      retriable: response.status >= 500,
      details: { status: response.status },
    });
  }
  return readResponseWithLimit(response, options.maxInputBytes, controller.signal);
}

function serializeError(error) {
  if (error instanceof GifInspectError) {
    return {
      code: error.code,
      category: error.category,
      message: error.message,
      retriable: error.retriable,
      ...(error.details ? { details: error.details } : {}),
    };
  }
  return {
    code: "INSPECTION_FAILED",
    category: "internal",
    message: error instanceof Error ? error.message : "GIF inspection failed.",
    retriable: false,
  };
}

function isValidJobId(jobId) {
  return (
    (typeof jobId === "string" && jobId.length > 0) ||
    (typeof jobId === "number" && Number.isFinite(jobId))
  );
}

const workerScope =
  typeof self !== "undefined" && typeof document === "undefined" && self?.postMessage
    ? self
    : null;
const activeJobs = new Map();

function postWorkerMessage(type, jobId, payload = {}) {
  workerScope?.postMessage({
    protocol: GIF_INSPECT_PROTOCOL,
    version: GIF_INSPECT_VERSION,
    type,
    jobId: isValidJobId(jobId) ? jobId : null,
    ...payload,
  });
}

async function runInspectJob(message) {
  const { jobId } = message;
  const controller = new AbortController();
  const job = { controller, cancelRequested: false };
  activeJobs.set(jobId, job);

  try {
    const options = normalizeOptions(message.options);
    const buffer = await loadSource(message.source, options, controller);
    const result = await inspectGifArrayBuffer(buffer, options, controller.signal);
    if (job.cancelRequested) {
      postWorkerMessage("cancelled", jobId, { active: true });
    } else {
      postWorkerMessage("result", jobId, { result });
    }
  } catch (error) {
    if (job.cancelRequested || controller.signal.aborted || error?.name === "AbortError") {
      postWorkerMessage("cancelled", jobId, { active: true });
    } else {
      postWorkerMessage("error", jobId, { error: serializeError(error) });
    }
  } finally {
    if (activeJobs.get(jobId) === job) {
      activeJobs.delete(jobId);
    }
  }
}

function handleWorkerMessage(event) {
  const message = event?.data;
  const jobId = message?.jobId;

  if (message?.protocol !== GIF_INSPECT_PROTOCOL) {
    postWorkerMessage("error", jobId, {
      error: serializeError(
        new GifInspectError("INVALID_PROTOCOL", `Expected protocol \"${GIF_INSPECT_PROTOCOL}\".`, {
          category: "protocol",
        })
      ),
    });
    return;
  }
  if (message?.version !== GIF_INSPECT_VERSION) {
    postWorkerMessage("error", jobId, {
      error: serializeError(
        new GifInspectError(
          "UNSUPPORTED_VERSION",
          `GIF inspection protocol version ${String(message?.version)} is not supported.`,
          {
            category: "capability",
            details: { supportedVersion: GIF_INSPECT_VERSION },
          }
        )
      ),
    });
    return;
  }
  if (!isValidJobId(jobId)) {
    postWorkerMessage("error", null, {
      error: serializeError(
        new GifInspectError("INVALID_JOB_ID", "jobId must be a non-empty string or finite number.", {
          category: "protocol",
        })
      ),
    });
    return;
  }

  if (message.type === "cancel") {
    const job = activeJobs.get(jobId);
    if (!job) {
      postWorkerMessage("cancelled", jobId, { active: false });
      return;
    }
    job.cancelRequested = true;
    job.controller.abort();
    return;
  }

  if (message.type !== "inspect") {
    postWorkerMessage("error", jobId, {
      error: serializeError(
        new GifInspectError("INVALID_MESSAGE_TYPE", 'Message type must be "inspect" or "cancel".', {
          category: "protocol",
        })
      ),
    });
    return;
  }
  if (activeJobs.has(jobId)) {
    postWorkerMessage("error", jobId, {
      error: serializeError(
        new GifInspectError("DUPLICATE_JOB_ID", "An active inspection already uses this jobId.", {
          category: "protocol",
        })
      ),
    });
    return;
  }

  void runInspectJob(message);
}

if (workerScope) {
  workerScope.addEventListener("message", handleWorkerMessage);
}
