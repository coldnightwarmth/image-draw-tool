import { decompressFrame, parseGIF } from "./gifuct-js.bundle.mjs";

/**
 * Brush export raster worker protocol v1
 * ======================================
 *
 * Create with:
 *   new Worker("./export-raster-worker.js", { type: "module" })
 *
 * Every request and response contains:
 *   { protocol: "brush-export-raster", version: 1, type, requestId?, jobId? }
 *
 * Requests:
 *   probe
 *     Runs a real OffscreenCanvas self-test. The worker also posts one
 *     unsolicited `ready` message after module startup.
 *
 *   prepare
 *     { jobId, scene, assets?, options?: { memoryBudgetBytes? } }
 *     Normalizes and owns a cloneable scene snapshot, fetches/decodes every
 *     referenced source, and replies with `prepared`. Reusing a jobId releases
 *     the previous job. A preparation error is terminal for the job so callers
 *     can fall back wholesale to the main-thread exporter.
 *
 *   render-frame (the alias `render` is also accepted)
 *     { jobId, timeMs?, output?: "png" | "rgba" | "bitmap", entries?, background? }
 *     Renders one frame and replies with `rendered`. Optional entries/background
 *     replace the prepared values for that frame; all referenced assets must
 *     have been declared during prepare. `rgba` transfers an ArrayBuffer and
 *     `bitmap` transfers an ImageBitmap.
 *
 *   render-frames
 *     { jobId, output?, frames: [{ timeMs?, entries?, background? }, ...] }
 *     Replies once with `frames-rendered`. Each result is the same payload used
 *     by `rendered`. This rasterizes only; it intentionally does not encode GIF
 *     or video and does not use MediaRecorder.
 *
 *   cancel | release
 *     { jobId }. Cancel aborts fetches and queued work. Release also closes all
 *     worker-owned ImageBitmaps and zeroes the job canvases.
 *
 * Scene DTO (all fields are structured-cloneable):
 *   {
 *     outputWidth, outputHeight,
 *     selectionBounds: { left, top, right, bottom },
 *     entries: StampDTO[],
 *     background?: BackgroundDTO,
 *     assets?: AssetDTO[]                 // may instead be beside `scene`
 *   }
 *
 * StampDTO array order is paint/z order and is never regrouped or reordered:
 *   {
 *     sourceId? | sourceUrl,
 *     centerX, centerY, width, height, rotation?, opacity?, blendMode?,
 *     imageRendering?: "auto" | "pixelated",
 *     tintSettings?: { color, amountPercent } | { layers: [...] },
 *     tintLayers?: [{ color, amountPercent }],
 *     colorMatrix?: number[20],           // normalized SVG 4x5 RGBA matrix
 *     pixelateAmount?, blurAmount?, phaseOffsetMs?, playbackRate?
 *   }
 *
 * BackgroundDTO:
 *   {
 *     include?: boolean, color?: "#rrggbb", matteColor?: string,
 *     image?: { sourceId? | sourceUrl, opacity?, mode?: "stretch" | "tile",
 *               tileSize?, phaseOffsetMs?, playbackRate? }
 *   }
 * `stretch` intentionally matches the existing exporter: aspect-fill/cover.
 *
 * AssetDTO:
 *   {
 *     id? | sourceId? | url,
 *     url?, mimeType?, kind?: "auto" | "gif" | "static",
 *     bytes?: ArrayBuffer | TypedArray, blob?: Blob, bitmap?: ImageBitmap,
 *     frames?: [{ bitmap: ImageBitmap, durationMs? }],
 *     workerOwnsBitmap?: boolean
 *   }
 * If no AssetDTO is supplied for a sourceUrl, the worker fetches it. GIF frame
 * composition mirrors app.js, including disposal methods 2 and 3 and the same
 * 20 ms minimum plus GIFuct-compatible missing/zero-delay timing.
 */

export const EXPORT_RASTER_PROTOCOL = "brush-export-raster";
export const EXPORT_RASTER_VERSION = 1;

const DEFAULT_GIF_FRAME_DELAY_MS = 50;
const MIN_GIF_FRAME_DELAY_MS = 20;
const MAX_SOURCE_BYTES = 256 * 1024 * 1024;
const MAX_OUTPUT_PIXELS = 128 * 1024 * 1024;
const MAX_OUTPUT_DIMENSION = 32768;
const MEBIBYTE = 1024 * 1024;
const MIN_REQUESTED_MEMORY_BUDGET_BYTES = 32 * MEBIBYTE;
const MIN_MEMORY_BUDGET_BYTES = 64 * MEBIBYTE;
const DEFAULT_MEMORY_BUDGET_BYTES = 384 * MEBIBYTE;
const MAX_MEMORY_BUDGET_BYTES = 768 * MEBIBYTE;
const MEMORY_BUDGET_BYTES_PER_DEVICE_GIB = 96 * MEBIBYTE;
const MIN_BITMAP_ALLOCATION_BYTES = 4096;
const MAX_DECODED_GIF_FRAMES = 20000;
const STAMP_YIELD_INTERVAL = 192;
const FRAME_LIMIT = 4096;
const workerScope = typeof self !== "undefined" ? self : null;
const jobs = new Map();

const BLEND_MODES = [
  "normal",
  "multiply",
  "screen",
  "overlay",
  "darken",
  "lighten",
  "color-dodge",
  "color-burn",
  "hard-light",
  "soft-light",
  "difference",
  "exclusion",
  "hue",
  "saturation",
  "color",
  "luminosity"
];

class ExportRasterError extends Error {
  constructor(code, message, options = {}) {
    super(message);
    this.name = "ExportRasterError";
    this.code = code;
    this.capability = options.capability === true;
    this.cancelled = options.cancelled === true;
    this.details = options.details || null;
  }
}

function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}

function finiteNumber(value, fallback = 0) {
  const numeric = Number(value);
  return Number.isFinite(numeric) ? numeric : fallback;
}

function positiveNumber(value, fallback = 1) {
  const numeric = Number(value);
  return Number.isFinite(numeric) && numeric > 0 ? numeric : fallback;
}

function getDeviceAwareMemoryBudgetBytes(requestedBytes = null) {
  const deviceMemoryGiB = Number(workerScope?.navigator?.deviceMemory);
  const detectedBudget = Number.isFinite(deviceMemoryGiB) && deviceMemoryGiB > 0
    ? deviceMemoryGiB * MEMORY_BUDGET_BYTES_PER_DEVICE_GIB
    : DEFAULT_MEMORY_BUDGET_BYTES;
  const automaticBudget = clamp(
    Math.round(detectedBudget),
    MIN_MEMORY_BUDGET_BYTES,
    MAX_MEMORY_BUDGET_BYTES
  );
  const requested = Number(requestedBytes);
  if (!Number.isFinite(requested) || requested <= 0) {
    return automaticBudget;
  }
  return Math.min(
    automaticBudget,
    clamp(
      Math.round(requested),
      MIN_REQUESTED_MEMORY_BUDGET_BYTES,
      MAX_MEMORY_BUDGET_BYTES
    )
  );
}

function getSafeRgbaByteLength(width, height, multiplier = 1) {
  const pixels = Number(width) * Number(height);
  const bytes = pixels * 4 * Number(multiplier);
  if (!Number.isSafeInteger(bytes) || bytes < 0) {
    throw new ExportRasterError("MEMORY_ESTIMATE_OVERFLOW", "A raster allocation is too large to estimate safely.", {
      capability: true,
      details: { width, height, multiplier }
    });
  }
  return bytes;
}

function getEstimatedBitmapByteLength(width, height) {
  return Math.max(MIN_BITMAP_ALLOCATION_BYTES, getSafeRgbaByteLength(width, height));
}

function getEstimatedBitmapSeriesByteLength(width, height, frameCount) {
  const perFrameBytes = getEstimatedBitmapByteLength(width, height);
  const bytes = perFrameBytes * Number(frameCount);
  if (!Number.isSafeInteger(bytes) || bytes < 0) {
    throw new ExportRasterError("MEMORY_ESTIMATE_OVERFLOW", "A bitmap series is too large to estimate safely.", {
      capability: true,
      details: { width, height, frameCount }
    });
  }
  return bytes;
}

function getProjectedJobMemoryBytes(
  job,
  { additionalDecodedBytes = 0, additionalCanvasBytes = 0, transientBytes = 0 } = {}
) {
  const decodedBytes = Math.max(0, Number(job?.decodedBitmapBytes) || 0) +
    Math.max(0, Number(additionalDecodedBytes) || 0);
  const activeWorkingBytes = Math.max(0, Number(job?.canvasBytes) || 0) +
    Math.max(0, Number(additionalCanvasBytes) || 0) +
    Math.max(0, Number(transientBytes) || 0);
  const reservedWorkingBytes = Math.max(0, Number(job?.outputWorkingSetReserveBytes) || 0);
  return decodedBytes + Math.max(activeWorkingBytes, reservedWorkingBytes);
}

function assertJobMemoryBudget(job, options = {}) {
  if (!job) {
    const standaloneBudget = getDeviceAwareMemoryBudgetBytes();
    const standaloneRequired = Math.max(0, Number(options.additionalDecodedBytes) || 0) +
      Math.max(0, Number(options.transientBytes) || 0);
    if (standaloneRequired <= standaloneBudget) {
      return;
    }
    throw new ExportRasterError(
      "MEMORY_BUDGET_EXCEEDED",
      "The raster operation exceeds the worker's safe memory budget.",
      {
        capability: true,
        details: {
          phase: options.phase || "raster",
          requiredBytes: standaloneRequired,
          budgetBytes: standaloneBudget
        }
      }
    );
  }
  const requiredBytes = getProjectedJobMemoryBytes(job, options);
  if (requiredBytes <= job.memoryBudgetBytes) {
    return;
  }
  throw new ExportRasterError(
    "MEMORY_BUDGET_EXCEEDED",
    "This export would exceed the worker's safe memory budget.",
    {
      capability: true,
      details: {
        phase: options.phase || "raster",
        requiredBytes,
        budgetBytes: job.memoryBudgetBytes,
        decodedBitmapBytes: job.decodedBitmapBytes,
        canvasBytes: job.canvasBytes,
        reservedOutputWorkingSetBytes: job.outputWorkingSetReserveBytes,
        additionalDecodedBytes: Math.max(0, Number(options.additionalDecodedBytes) || 0),
        additionalCanvasBytes: Math.max(0, Number(options.additionalCanvasBytes) || 0),
        transientBytes: Math.max(0, Number(options.transientBytes) || 0)
      }
    }
  );
}

function getAvailableTransientBytes(job) {
  if (!job) {
    return getDeviceAwareMemoryBudgetBytes();
  }
  return Math.max(
    0,
    job.memoryBudgetBytes - job.decodedBitmapBytes - job.canvasBytes
  );
}

function reserveDecodedBitmapBytes(job, byteLength, options = {}) {
  const bytes = Math.max(0, Math.round(Number(byteLength) || 0));
  assertJobMemoryBudget(job, { ...options, additionalDecodedBytes: bytes });
  if (job) {
    job.decodedBitmapBytes += bytes;
  }
  return bytes;
}

function releaseDecodedBitmapBytes(job, byteLength) {
  if (!job) {
    return;
  }
  job.decodedBitmapBytes = Math.max(
    0,
    job.decodedBitmapBytes - Math.max(0, Math.round(Number(byteLength) || 0))
  );
}

function normalizeJobId(value) {
  if ((typeof value === "string" && value) || (typeof value === "number" && Number.isFinite(value))) {
    return String(value);
  }
  throw new ExportRasterError("INVALID_JOB_ID", "A non-empty jobId is required.");
}

function normalizeSourceId(value) {
  if ((typeof value === "string" && value) || (typeof value === "number" && Number.isFinite(value))) {
    return String(value);
  }
  return "";
}

function getRequestId(message) {
  return message?.requestId ?? message?.id ?? null;
}

function serializeError(error) {
  if (error instanceof ExportRasterError) {
    return {
      code: error.code,
      message: error.message,
      capability: error.capability,
      cancelled: error.cancelled,
      ...(error.details ? { details: error.details } : {})
    };
  }
  if (error?.name === "AbortError") {
    return {
      code: "CANCELLED",
      message: "Export raster work was cancelled.",
      capability: false,
      cancelled: true
    };
  }
  return {
    code: "EXPORT_RASTER_FAILURE",
    message: error instanceof Error ? error.message : "The export raster worker failed.",
    capability: false,
    cancelled: false
  };
}

function post(type, payload = {}, transfer = []) {
  workerScope?.postMessage(
    {
      protocol: EXPORT_RASTER_PROTOCOL,
      version: EXPORT_RASTER_VERSION,
      type,
      ...payload
    },
    transfer
  );
}

function postError(action, error, message = null) {
  post("error", {
    action,
    fallback: true,
    ...(message?.jobId != null ? { jobId: String(message.jobId) } : {}),
    ...(getRequestId(message) != null ? { requestId: getRequestId(message) } : {}),
    error: serializeError(error)
  });
}

function throwIfCancelled(job) {
  if (job?.cancelled || job?.released) {
    throw new ExportRasterError("CANCELLED", "Export raster work was cancelled.", {
      cancelled: true
    });
  }
}

function yieldToWorker(job) {
  return new Promise((resolve, reject) => {
    setTimeout(() => {
      try {
        throwIfCancelled(job);
        resolve();
      } catch (error) {
        reject(error);
      }
    }, 0);
  });
}

function normalizeBounds(raw, outputWidth, outputHeight) {
  const value = raw && typeof raw === "object" ? raw : {};
  const left = finiteNumber(value.left ?? value.x, 0);
  const top = finiteNumber(value.top ?? value.y, 0);
  let right = Number(value.right);
  let bottom = Number(value.bottom);
  if (!Number.isFinite(right)) {
    right = left + positiveNumber(value.width, outputWidth);
  }
  if (!Number.isFinite(bottom)) {
    bottom = top + positiveNumber(value.height, outputHeight);
  }
  if (!(right > left) || !(bottom > top)) {
    throw new ExportRasterError("INVALID_BOUNDS", "selectionBounds must have positive width and height.");
  }
  return { left, top, right, bottom };
}

function normalizeHexColor(value, fallback = "#ffffff") {
  const color = typeof value === "string" ? value.trim().toLowerCase() : "";
  if (/^#[0-9a-f]{6}$/i.test(color)) {
    return color;
  }
  if (/^#[0-9a-f]{3}$/i.test(color)) {
    return `#${color[1]}${color[1]}${color[2]}${color[2]}${color[3]}${color[3]}`;
  }
  return fallback;
}

function normalizeTintLayers(raw) {
  const settings = raw?.tintSettings ?? raw?.tint ?? null;
  const candidates = Array.isArray(raw?.tintLayers)
    ? raw.tintLayers
    : Array.isArray(settings?.layers)
    ? settings.layers
    : settings
    ? [settings]
    : [];
  return candidates
    .map((layer) => ({
      color: normalizeHexColor(layer?.color, "#ffffff"),
      amountPercent: clamp(finiteNumber(layer?.amountPercent ?? layer?.amount, 0), 0, 100)
    }))
    .filter((layer) => layer.amountPercent > 0);
}

function normalizeColorMatrix(value) {
  const values = Array.isArray(value) || ArrayBuffer.isView(value) ? Array.from(value, Number) : [];
  if (values.length === 0) {
    return null;
  }
  if (values.length !== 20 || values.some((item) => !Number.isFinite(item))) {
    throw new ExportRasterError("INVALID_COLOR_MATRIX", "colorMatrix must contain 20 finite numbers.");
  }
  return values;
}

function normalizeBlendMode(value) {
  const mode = String(value || "normal");
  if (!BLEND_MODES.includes(mode)) {
    throw new ExportRasterError("UNSUPPORTED_BLEND_MODE", `Unsupported blend mode: ${mode}.`, {
      capability: true
    });
  }
  return mode;
}

function normalizeEntry(raw, index) {
  if (!raw || typeof raw !== "object") {
    throw new ExportRasterError("INVALID_STAMP", `Stamp ${index} must be an object.`);
  }
  const sourceUrl = typeof raw.sourceUrl === "string" ? raw.sourceUrl : "";
  const sourceId = normalizeSourceId(raw.sourceId ?? raw.assetId ?? sourceUrl);
  if (!sourceId) {
    throw new ExportRasterError("INVALID_STAMP_SOURCE", `Stamp ${index} has no sourceId or sourceUrl.`);
  }
  const width = Number(raw.width);
  const height = Number(raw.height);
  if (!Number.isFinite(width) || width <= 0 || !Number.isFinite(height) || height <= 0) {
    throw new ExportRasterError("INVALID_STAMP_GEOMETRY", `Stamp ${index} width and height must be positive.`);
  }
  const centerX = Number.isFinite(Number(raw.centerX))
    ? Number(raw.centerX)
    : finiteNumber(raw.left, 0) + width / 2;
  const centerY = Number.isFinite(Number(raw.centerY))
    ? Number(raw.centerY)
    : finiteNumber(raw.top, 0) + height / 2;
  const opacity = finiteNumber(raw.opacity, 1);
  if (opacity < 0 || opacity > 1) {
    throw new ExportRasterError("INVALID_STAMP_OPACITY", `Stamp ${index} opacity must be from 0 to 1.`);
  }
  return {
    sourceId,
    sourceUrl,
    centerX,
    centerY,
    width,
    height,
    rotation: finiteNumber(raw.rotation, 0),
    opacity,
    blendMode: normalizeBlendMode(raw.blendMode),
    imageRendering: raw.imageRendering === "auto" ? "auto" : "pixelated",
    tintLayers: normalizeTintLayers(raw),
    colorMatrix: normalizeColorMatrix(raw.colorMatrix ?? raw.tintColorMatrix),
    pixelateAmount: clamp(Math.round(finiteNumber(raw.pixelateAmount, 0)), 0, 64),
    blurAmount: clamp(finiteNumber(raw.blurAmount, 0), 0, 64),
    phaseOffsetMs: finiteNumber(raw.phaseOffsetMs, 0),
    playbackRate: Math.max(0, finiteNumber(raw.playbackRate, 1))
  };
}

function normalizeBackground(raw, fallback = null) {
  const base = fallback && typeof fallback === "object" ? fallback : {};
  const value = raw && typeof raw === "object" ? raw : {};
  const explicitlyClearsImage = Object.prototype.hasOwnProperty.call(value, "image") && value.image == null;
  const imageRaw = explicitlyClearsImage
    ? null
    : value.image && typeof value.image === "object"
    ? value.image
    : value.imageUrl || value.sourceUrl
    ? value
    : base.image || null;
  let image = null;
  if (imageRaw) {
    const sourceUrl = typeof imageRaw.sourceUrl === "string"
      ? imageRaw.sourceUrl
      : typeof imageRaw.url === "string"
      ? imageRaw.url
      : "";
    const sourceId = normalizeSourceId(imageRaw.sourceId ?? imageRaw.assetId ?? sourceUrl);
    if (!sourceId) {
      throw new ExportRasterError("INVALID_BACKGROUND_SOURCE", "The background image has no sourceId or sourceUrl.");
    }
    image = {
      sourceId,
      sourceUrl,
      opacity: clamp(finiteNumber(imageRaw.opacity, 1), 0, 1),
      mode: imageRaw.mode === "tile" ? "tile" : "stretch",
      tileSize: Math.max(1, finiteNumber(imageRaw.tileSize, 150)),
      phaseOffsetMs: finiteNumber(imageRaw.phaseOffsetMs, 0),
      playbackRate: Math.max(0, finiteNumber(imageRaw.playbackRate, 1))
    };
  }
  return {
    include: value.include == null ? base.include !== false : value.include !== false,
    color: normalizeHexColor(value.color ?? base.color, "#ffffff"),
    matteColor: typeof value.matteColor === "string"
      ? value.matteColor
      : typeof base.matteColor === "string"
      ? base.matteColor
      : "",
    image
  };
}

function normalizeScene(raw) {
  if (!raw || typeof raw !== "object") {
    throw new ExportRasterError("INVALID_SCENE", "prepare requires a scene object.");
  }
  const outputWidth = Math.round(Number(raw.outputWidth ?? raw.width));
  const outputHeight = Math.round(Number(raw.outputHeight ?? raw.height));
  if (
    !Number.isFinite(outputWidth) ||
    !Number.isFinite(outputHeight) ||
    outputWidth < 1 ||
    outputHeight < 1 ||
    outputWidth > MAX_OUTPUT_DIMENSION ||
    outputHeight > MAX_OUTPUT_DIMENSION ||
    outputWidth * outputHeight > MAX_OUTPUT_PIXELS
  ) {
    throw new ExportRasterError(
      "INVALID_OUTPUT_SIZE",
      `Output dimensions must be positive, at most ${MAX_OUTPUT_DIMENSION}px each, and within the worker pixel limit.`,
      { capability: true }
    );
  }
  const entries = Array.isArray(raw.entries)
    ? raw.entries.map((entry, index) => normalizeEntry(entry, index))
    : [];
  const legacyBackground = {
    include: raw.includeBackground !== false,
    color: raw.backgroundColor,
    matteColor: raw.matteColor,
    image: raw.backgroundImage || null
  };
  return {
    outputWidth,
    outputHeight,
    singleGifFrameTimeMs:
      raw.singleGifFrameTimeMs != null &&
      Number.isFinite(Number(raw.singleGifFrameTimeMs))
      ? Math.max(0, Number(raw.singleGifFrameTimeMs))
      : null,
    selectionBounds: normalizeBounds(raw.selectionBounds ?? raw.bounds, outputWidth, outputHeight),
    entries,
    background: normalizeBackground(raw.background, legacyBackground)
  };
}

function normalizeAssetDescriptor(raw, fallbackId = "", fallbackUrl = "") {
  const value = raw && typeof raw === "object" ? raw : {};
  const url = typeof value.url === "string"
    ? value.url
    : typeof value.sourceUrl === "string"
    ? value.sourceUrl
    : fallbackUrl;
  const id = normalizeSourceId(value.id ?? value.sourceId ?? value.assetId ?? fallbackId ?? url);
  if (!id) {
    throw new ExportRasterError("INVALID_ASSET", "Every asset needs an id/sourceId or URL.");
  }
  const kind = ["gif", "static"].includes(value.kind) ? value.kind : "auto";
  return {
    ...value,
    id,
    url,
    kind,
    mimeType: typeof value.mimeType === "string" ? value.mimeType : "",
    targetWidth: Math.max(0, finiteNumber(value.targetWidth, 0)),
    targetHeight: Math.max(0, finiteNumber(value.targetHeight, 0)),
    frameIntervalMs: Math.max(
      MIN_GIF_FRAME_DELAY_MS,
      finiteNumber(value.frameIntervalMs, MIN_GIF_FRAME_DELAY_MS)
    ),
    imageSmoothing: value.imageSmoothing !== false,
    decodeBudgetBytes: Math.max(0, finiteNumber(value.decodeBudgetBytes, 0)),
    singleFrameTimeMs:
      value.singleFrameTimeMs != null &&
      Number.isFinite(Number(value.singleFrameTimeMs))
      ? Math.max(0, Number(value.singleFrameTimeMs))
      : null
  };
}

function collectAssetDescriptors(scene, rawAssets) {
  const descriptors = new Map();
  const supplied = Array.isArray(rawAssets) ? rawAssets : [];
  for (const raw of supplied) {
    const descriptor = normalizeAssetDescriptor(raw);
    if (descriptors.has(descriptor.id)) {
      throw new ExportRasterError("DUPLICATE_ASSET", `Asset id ${descriptor.id} was declared more than once.`);
    }
    descriptors.set(descriptor.id, descriptor);
  }
  const addReference = (sourceId, sourceUrl) => {
    if (!descriptors.has(sourceId)) {
      descriptors.set(sourceId, normalizeAssetDescriptor({}, sourceId, sourceUrl));
    } else {
      const descriptor = descriptors.get(sourceId);
      if (!descriptor.url && sourceUrl) {
        descriptor.url = sourceUrl;
      }
    }
  };
  for (const entry of scene.entries) {
    addReference(entry.sourceId, entry.sourceUrl);
  }
  if (scene.background.image) {
    addReference(scene.background.image.sourceId, scene.background.image.sourceUrl);
  }

  const selectionWidth = Math.max(1, scene.selectionBounds.right - scene.selectionBounds.left);
  const selectionHeight = Math.max(1, scene.selectionBounds.bottom - scene.selectionBounds.top);
  const scaleX = scene.outputWidth / selectionWidth;
  const scaleY = scene.outputHeight / selectionHeight;
  const usageBySourceId = new Map();
  for (const entry of scene.entries) {
    let usage = usageBySourceId.get(entry.sourceId);
    if (!usage) {
      usage = { width: 1, height: 1, imageSmoothing: false };
      usageBySourceId.set(entry.sourceId, usage);
    }
    usage.width = Math.max(usage.width, Math.ceil(Math.abs(entry.width * scaleX) * 1.25));
    usage.height = Math.max(usage.height, Math.ceil(Math.abs(entry.height * scaleY) * 1.25));
    usage.imageSmoothing ||= entry.imageRendering === "auto";
  }
  if (scene.background.image) {
    const sourceId = scene.background.image.sourceId;
    const usage = usageBySourceId.get(sourceId) || { width: 1, height: 1, imageSmoothing: true };
    if (scene.background.image.mode === "tile") {
      const tileWidth = Math.ceil(scene.background.image.tileSize * scaleX * 1.25);
      usage.width = Math.max(usage.width, tileWidth);
    } else {
      usage.width = Math.max(usage.width, scene.outputWidth);
      usage.height = Math.max(usage.height, scene.outputHeight);
    }
    usage.imageSmoothing = true;
    usageBySourceId.set(sourceId, usage);
  }
  for (const [sourceId, descriptor] of descriptors) {
    const usage = usageBySourceId.get(sourceId);
    if (!usage) {
      continue;
    }
    descriptor.targetWidth = Math.max(descriptor.targetWidth || 0, usage.width);
    descriptor.targetHeight = Math.max(descriptor.targetHeight || 0, usage.height);
    descriptor.imageSmoothing = descriptor.imageSmoothing !== false && usage.imageSmoothing;
    if (scene.singleGifFrameTimeMs !== null) {
      descriptor.singleFrameTimeMs = scene.singleGifFrameTimeMs;
    }
  }
  return descriptors;
}

function normalizeArrayBuffer(value) {
  if (value instanceof ArrayBuffer) {
    return value;
  }
  if (ArrayBuffer.isView(value)) {
    return value.buffer.slice(value.byteOffset, value.byteOffset + value.byteLength);
  }
  return null;
}

function hasGifSignature(bytes) {
  if (!bytes || bytes.byteLength < 6) {
    return false;
  }
  const view = new Uint8Array(bytes, 0, 6);
  const signature = String.fromCharCode(...view);
  return signature === "GIF87a" || signature === "GIF89a";
}

function asciiAt(bytes, offset, length) {
  const view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
  if (offset < 0 || offset + length > view.length) {
    return "";
  }
  let value = "";
  for (let index = 0; index < length; index += 1) {
    value += String.fromCharCode(view[offset + index]);
  }
  return value;
}

function readUint24LittleEndian(bytes, offset) {
  return bytes[offset] + (bytes[offset + 1] << 8) + (bytes[offset + 2] << 16);
}

function sniffJpegDimensions(bytes) {
  if (bytes.length < 4 || bytes[0] !== 0xff || bytes[1] !== 0xd8) {
    return null;
  }
  const standaloneMarkers = new Set([0x01, 0xd8, 0xd9, 0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7]);
  const startOfFrameMarkers = new Set([
    0xc0, 0xc1, 0xc2, 0xc3, 0xc5, 0xc6, 0xc7, 0xc9, 0xca, 0xcb, 0xcd, 0xce, 0xcf
  ]);
  let offset = 2;
  while (offset + 3 < bytes.length) {
    while (offset < bytes.length && bytes[offset] !== 0xff) {
      offset += 1;
    }
    while (offset < bytes.length && bytes[offset] === 0xff) {
      offset += 1;
    }
    if (offset >= bytes.length) {
      break;
    }
    const marker = bytes[offset];
    offset += 1;
    if (standaloneMarkers.has(marker)) {
      continue;
    }
    if (offset + 1 >= bytes.length) {
      break;
    }
    const segmentLength = (bytes[offset] << 8) | bytes[offset + 1];
    if (segmentLength < 2 || offset + segmentLength > bytes.length) {
      break;
    }
    if (startOfFrameMarkers.has(marker) && segmentLength >= 7) {
      const height = (bytes[offset + 3] << 8) | bytes[offset + 4];
      const width = (bytes[offset + 5] << 8) | bytes[offset + 6];
      return width > 0 && height > 0 ? { width, height, format: "jpeg" } : null;
    }
    offset += segmentLength;
  }
  return null;
}

function sniffWebpDimensions(bytes) {
  if (bytes.length < 16 || asciiAt(bytes, 0, 4) !== "RIFF" || asciiAt(bytes, 8, 4) !== "WEBP") {
    return null;
  }
  let offset = 12;
  while (offset + 8 <= bytes.length) {
    const chunkType = asciiAt(bytes, offset, 4);
    const chunkLength =
      bytes[offset + 4] +
      (bytes[offset + 5] << 8) +
      (bytes[offset + 6] << 16) +
      bytes[offset + 7] * 0x1000000;
    const dataOffset = offset + 8;
    if (chunkType === "VP8X" && dataOffset + 10 <= bytes.length) {
      return {
        width: readUint24LittleEndian(bytes, dataOffset + 4) + 1,
        height: readUint24LittleEndian(bytes, dataOffset + 7) + 1,
        format: "webp"
      };
    }
    if (chunkType === "VP8L" && dataOffset + 5 <= bytes.length && bytes[dataOffset] === 0x2f) {
      const width = 1 + bytes[dataOffset + 1] + ((bytes[dataOffset + 2] & 0x3f) << 8);
      const height = 1 +
        ((bytes[dataOffset + 2] & 0xc0) >> 6) +
        (bytes[dataOffset + 3] << 2) +
        ((bytes[dataOffset + 4] & 0x0f) << 10);
      return { width, height, format: "webp" };
    }
    if (
      chunkType === "VP8 " &&
      dataOffset + 10 <= bytes.length &&
      bytes[dataOffset + 3] === 0x9d &&
      bytes[dataOffset + 4] === 0x01 &&
      bytes[dataOffset + 5] === 0x2a
    ) {
      const width = (bytes[dataOffset + 6] | (bytes[dataOffset + 7] << 8)) & 0x3fff;
      const height = (bytes[dataOffset + 8] | (bytes[dataOffset + 9] << 8)) & 0x3fff;
      return width > 0 && height > 0 ? { width, height, format: "webp" } : null;
    }
    if (!Number.isFinite(chunkLength) || chunkLength < 0) {
      break;
    }
    offset = dataOffset + chunkLength + (chunkLength % 2);
  }
  return null;
}

function sniffStaticRasterDimensions(arrayBuffer) {
  const bytes = new Uint8Array(arrayBuffer);
  if (hasGifSignature(arrayBuffer) && bytes.length >= 10) {
    const width = bytes[6] | (bytes[7] << 8);
    const height = bytes[8] | (bytes[9] << 8);
    return width > 0 && height > 0 ? { width, height, format: "gif" } : null;
  }
  if (
    bytes.length >= 24 &&
    bytes[0] === 0x89 &&
    asciiAt(bytes, 1, 3) === "PNG" &&
    bytes[4] === 0x0d &&
    bytes[5] === 0x0a
  ) {
    const view = new DataView(arrayBuffer, 0, Math.min(arrayBuffer.byteLength, 24));
    const width = view.getUint32(16, false);
    const height = view.getUint32(20, false);
    return width > 0 && height > 0 ? { width, height, format: "png" } : null;
  }
  const jpeg = sniffJpegDimensions(bytes);
  if (jpeg) {
    return jpeg;
  }
  const webp = sniffWebpDimensions(bytes);
  if (webp) {
    return webp;
  }
  if (bytes.length >= 26 && asciiAt(bytes, 0, 2) === "BM") {
    const view = new DataView(arrayBuffer);
    const width = Math.abs(view.getInt32(18, true));
    const height = Math.abs(view.getInt32(22, true));
    return width > 0 && height > 0 ? { width, height, format: "bmp" } : null;
  }
  return null;
}

async function readAssetBytes(descriptor, job) {
  let mimeType = descriptor.mimeType || "";
  const direct = normalizeArrayBuffer(descriptor.bytes ?? descriptor.buffer ?? descriptor.data);
  if (direct) {
    if (direct.byteLength > MAX_SOURCE_BYTES) {
      throw new ExportRasterError("SOURCE_TOO_LARGE", `Asset ${descriptor.id} exceeds the worker byte limit.`);
    }
    assertJobMemoryBudget(job, {
      phase: "asset-input",
      transientBytes: direct.byteLength
    });
    return { bytes: direct, mimeType };
  }
  if (descriptor.blob instanceof Blob) {
    if (descriptor.blob.size > MAX_SOURCE_BYTES) {
      throw new ExportRasterError("SOURCE_TOO_LARGE", `Asset ${descriptor.id} exceeds the worker byte limit.`);
    }
    assertJobMemoryBudget(job, {
      phase: "asset-blob-read",
      transientBytes: descriptor.blob.size * 2
    });
    mimeType ||= descriptor.blob.type || "";
    return { bytes: await descriptor.blob.arrayBuffer(), mimeType };
  }
  if (!descriptor.url) {
    throw new ExportRasterError("MISSING_ASSET_SOURCE", `Asset ${descriptor.id} has no decodable source.`);
  }
  const controller = new AbortController();
  job.abortControllers.add(controller);
  try {
    const response = await fetch(descriptor.url, { signal: controller.signal });
    if (!response.ok) {
      throw new ExportRasterError(
        "ASSET_FETCH_FAILED",
        `Could not fetch asset ${descriptor.id} (${response.status}).`
      );
    }
    const declaredLength = Number(response.headers.get("content-length"));
    if (Number.isFinite(declaredLength) && declaredLength > MAX_SOURCE_BYTES) {
      throw new ExportRasterError("SOURCE_TOO_LARGE", `Asset ${descriptor.id} exceeds the worker byte limit.`);
    }
    if (Number.isFinite(declaredLength) && declaredLength >= 0) {
      assertJobMemoryBudget(job, {
        phase: "asset-fetch",
        transientBytes: declaredLength * 2
      });
    }
    mimeType ||= response.headers.get("content-type") || "";
    let bytes;
    if (response.body?.getReader) {
      const reader = response.body.getReader();
      const chunks = [];
      let byteLength = 0;
      const maximumStreamBytes = Math.min(
        MAX_SOURCE_BYTES,
        Math.floor(getAvailableTransientBytes(job) / 2)
      );
      try {
        while (true) {
          throwIfCancelled(job);
          const { value, done } = await reader.read();
          if (done) {
            break;
          }
          if (!value?.byteLength) {
            continue;
          }
          byteLength += value.byteLength;
          if (byteLength > maximumStreamBytes) {
            assertJobMemoryBudget(job, {
              phase: "asset-stream",
              transientBytes: byteLength * 2
            });
            throw new ExportRasterError(
              "SOURCE_TOO_LARGE",
              `Asset ${descriptor.id} exceeds the worker's safe stream limit.`,
              {
                capability: true,
                details: { byteLength, maximumStreamBytes }
              }
            );
          }
          chunks.push(value);
        }
        assertJobMemoryBudget(job, {
          phase: "asset-stream-assembly",
          transientBytes: byteLength * 2
        });
        const combined = new Uint8Array(byteLength);
        let writeOffset = 0;
        for (const chunk of chunks) {
          combined.set(chunk, writeOffset);
          writeOffset += chunk.byteLength;
        }
        chunks.length = 0;
        bytes = combined.buffer;
      } catch (error) {
        try {
          await reader.cancel(error);
        } catch (_cancelError) {
          // The response may already be closed after a network failure.
        }
        throw error;
      }
    } else {
      if (!Number.isFinite(declaredLength) || declaredLength < 0) {
        throw new ExportRasterError(
          "SOURCE_LENGTH_UNAVAILABLE",
          `Asset ${descriptor.id} cannot be read safely without a stream or content length.`,
          { capability: true }
        );
      }
      bytes = await response.arrayBuffer();
    }
    if (bytes.byteLength > MAX_SOURCE_BYTES) {
      throw new ExportRasterError("SOURCE_TOO_LARGE", `Asset ${descriptor.id} exceeds the worker byte limit.`);
    }
    assertJobMemoryBudget(job, {
      phase: "asset-input",
      transientBytes: bytes.byteLength
    });
    return { bytes, mimeType };
  } finally {
    job.abortControllers.delete(controller);
  }
}

function ownBitmap(job, bitmap, owned = true) {
  if (owned && bitmap && typeof bitmap.close === "function") {
    job.ownedBitmaps.add(bitmap);
  }
  return bitmap;
}

function normalizeProvidedFrames(descriptor, job) {
  if (!Array.isArray(descriptor.frames) || descriptor.frames.length === 0) {
    return null;
  }
  const frames = descriptor.frames.map((frame, index) => {
    const bitmap = frame?.bitmap;
    if (!bitmap || !Number.isFinite(Number(bitmap.width)) || !Number.isFinite(Number(bitmap.height))) {
      throw new ExportRasterError("INVALID_ASSET_FRAME", `Asset ${descriptor.id} frame ${index} is invalid.`);
    }
    return {
      bitmap,
      durationMs: Math.max(
        MIN_GIF_FRAME_DELAY_MS,
        finiteNumber(frame.durationMs ?? frame.delayMs, DEFAULT_GIF_FRAME_DELAY_MS)
      )
    };
  });
  const estimatedBitmapBytes = frames.reduce(
    (sum, frame) => sum + getEstimatedBitmapByteLength(frame.bitmap.width, frame.bitmap.height),
    0
  );
  if (!Number.isSafeInteger(estimatedBitmapBytes)) {
    if (descriptor.workerOwnsBitmap !== false) {
      for (const frame of frames) {
        frame.bitmap.close?.();
      }
    }
    throw new ExportRasterError("MEMORY_ESTIMATE_OVERFLOW", `Asset ${descriptor.id} has too many bitmap frames.`, {
      capability: true
    });
  }
  let reservedBytes = 0;
  try {
    reservedBytes = reserveDecodedBitmapBytes(job, estimatedBitmapBytes, {
      phase: "provided-frames"
    });
    for (const frame of frames) {
      ownBitmap(job, frame.bitmap, descriptor.workerOwnsBitmap !== false);
    }
  } catch (error) {
    if (descriptor.workerOwnsBitmap !== false) {
      for (const frame of frames) {
        frame.bitmap.close?.();
      }
    }
    releaseDecodedBitmapBytes(job, reservedBytes);
    throw error;
  }
  const width = Math.max(1, Math.round(frames[0].bitmap.width));
  const height = Math.max(1, Math.round(frames[0].bitmap.height));
  const kind = descriptor.kind === "gif" || frames.length > 1 ? "gif" : "static";
  const totalDurationMs = kind === "gif"
    ? frames.reduce((sum, frame) => sum + frame.durationMs, 0)
    : 0;
  return {
    id: descriptor.id,
    kind,
    width,
    height,
    frames,
    totalDurationMs,
    estimatedBitmapBytes
  };
}

function getRawGifFrameDelayMs(frame) {
  const centiseconds = Number(frame?.gce?.delay);
  if (!frame?.gce) {
    return DEFAULT_GIF_FRAME_DELAY_MS;
  }
  return Math.max(
    MIN_GIF_FRAME_DELAY_MS,
    Number.isFinite(centiseconds) && centiseconds > 0
      ? Math.round(centiseconds * 10)
      : 100
  );
}

function getGifLogicalBackgroundColor(parsed, imageFrames) {
  const hasTransparentFrames = imageFrames.some(
    (frame) => frame?.gce?.extras?.transparentColorGiven === true
  );
  if (hasTransparentFrames || !Array.isArray(parsed?.gct)) {
    return "";
  }
  const backgroundIndex = Number(parsed?.lsd?.backgroundColorIndex);
  const color = Number.isInteger(backgroundIndex) ? parsed.gct[backgroundIndex] : null;
  if (!Array.isArray(color) || color.length < 3) {
    return "";
  }
  const red = clamp(Math.round(finiteNumber(color[0], 0)), 0, 255);
  const green = clamp(Math.round(finiteNumber(color[1], 0)), 0, 255);
  const blue = clamp(Math.round(finiteNumber(color[2], 0)), 0, 255);
  return `rgb(${red}, ${green}, ${blue})`;
}

function getDecodeTargetDimensions(width, height, options = {}) {
  const requestedWidth = Math.max(1, finiteNumber(options.targetWidth, width));
  const requestedHeight = Math.max(1, finiteNumber(options.targetHeight, height));
  const scale = Math.min(1, Math.max(requestedWidth / width, requestedHeight / height));
  return {
    width: Math.max(1, Math.round(width * scale)),
    height: Math.max(1, Math.round(height * scale))
  };
}

function getAvailableDecodedBytes(job, transientBytes = 0) {
  if (!job) {
    return Math.max(0, getDeviceAwareMemoryBudgetBytes() - transientBytes);
  }
  const activeWorkingBytes = Math.max(
    job.outputWorkingSetReserveBytes || 0,
    (job.canvasBytes || 0) + Math.max(0, transientBytes)
  );
  return Math.max(0, job.memoryBudgetBytes - job.decodedBitmapBytes - activeWorkingBytes);
}

function estimateStoredGifFrameCount(frameDurations, intervalMs, maximumFrames) {
  if (!frameDurations.length || maximumFrames <= 0) {
    return 0;
  }
  if (maximumFrames === 1) {
    return 1;
  }
  let count = 0;
  let elapsedSinceStoredFrame = Infinity;
  for (let index = 0; index < frameDurations.length; index += 1) {
    const isLast = index === frameDurations.length - 1;
    const shouldStore =
      index === 0 ||
      (isLast && count < maximumFrames) ||
      (elapsedSinceStoredFrame >= intervalMs && count < maximumFrames - 1);
    if (shouldStore) {
      count += 1;
      elapsedSinceStoredFrame = frameDurations[index];
    } else {
      elapsedSinceStoredFrame += frameDurations[index];
    }
  }
  return count;
}

export async function decodeGifBytes(arrayBuffer, cancellationJob = null, options = {}) {
  const parseInput = normalizeArrayBuffer(arrayBuffer);
  if (!parseInput) {
    throw new ExportRasterError("INVALID_GIF_SOURCE", "GIF decode requires an ArrayBuffer or typed array.");
  }
  let parsed;
  try {
    parsed = parseGIF(parseInput);
  } catch (error) {
    throw new ExportRasterError("GIF_DECODE_FAILED", "The GIF could not be decoded.", {
      details: { cause: error instanceof Error ? error.message : "unknown error" }
    });
  }
  const imageFrames = Array.isArray(parsed?.frames)
    ? parsed.frames.filter((frame) => frame?.image)
    : [];
  if (!imageFrames.length) {
    throw new ExportRasterError("GIF_DECODE_FAILED", "The GIF contains no decodable frames.");
  }
  if (imageFrames.length > MAX_DECODED_GIF_FRAMES) {
    throw new ExportRasterError(
      "GIF_FRAME_LIMIT_EXCEEDED",
      `The GIF exceeds the worker frame limit of ${MAX_DECODED_GIF_FRAMES}.`,
      { capability: true, details: { frameCount: imageFrames.length } }
    );
  }
  const firstDescriptor = imageFrames[0]?.image?.descriptor || {};
  const width = Math.max(1, Number(parsed?.lsd?.width) || Number(firstDescriptor.width) || 1);
  const height = Math.max(1, Number(parsed?.lsd?.height) || Number(firstDescriptor.height) || 1);
  const logicalFrameBytes = getSafeRgbaByteLength(width, height);
  const frameDurations = imageFrames.map(getRawGifFrameDelayMs);
  const logicalBackgroundColor = getGifLogicalBackgroundColor(parsed, imageFrames);
  const totalSourceDurationMs =
    frameDurations.reduce((sum, duration) => sum + duration, 0) || DEFAULT_GIF_FRAME_DELAY_MS;
  const singleFrameMode =
    options.singleFrameTimeMs != null &&
    Number.isFinite(Number(options.singleFrameTimeMs));
  let singleFrameIndex = -1;
  if (singleFrameMode) {
    let wrappedTimeMs = Math.max(0, Number(options.singleFrameTimeMs)) % totalSourceDurationMs;
    singleFrameIndex = frameDurations.length - 1;
    for (let index = 0; index < frameDurations.length; index += 1) {
      if (wrappedTimeMs < frameDurations[index]) {
        singleFrameIndex = index;
        break;
      }
      wrappedTimeMs -= frameDurations[index];
    }
  }
  let targetDimensions = getDecodeTargetDimensions(width, height, options);
  let maximumPatchBytes = 4;
  let needsRestoreSnapshot = false;
  for (const frame of imageFrames) {
    const descriptor = frame?.image?.descriptor || {};
    const frameWidth = Math.max(1, Number(descriptor.width) || width);
    const frameHeight = Math.max(1, Number(descriptor.height) || height);
    maximumPatchBytes = Math.max(maximumPatchBytes, getSafeRgbaByteLength(frameWidth, frameHeight));
    needsRestoreSnapshot ||= Number(frame?.gce?.extras?.disposal) === 3;
  }
  const decodeTransientBytes =
    parseInput.byteLength +
    logicalFrameBytes +
    maximumPatchBytes * 2 +
    (needsRestoreSnapshot ? logicalFrameBytes : 0) +
    getSafeRgbaByteLength(targetDimensions.width, targetDimensions.height);
  const requestedDecodeBudget = Math.max(
    MIN_BITMAP_ALLOCATION_BYTES,
    finiteNumber(options.decodeBudgetBytes, getAvailableDecodedBytes(cancellationJob, decodeTransientBytes))
  );
  const availableDecodeBudget = Math.min(
    requestedDecodeBudget,
    getAvailableDecodedBytes(cancellationJob, decodeTransientBytes)
  );
  let bytesPerStoredFrame = getEstimatedBitmapByteLength(
    targetDimensions.width,
    targetDimensions.height
  );
  if (bytesPerStoredFrame > availableDecodeBudget && availableDecodeBudget >= MIN_BITMAP_ALLOCATION_BYTES) {
    const memoryScale = Math.sqrt(availableDecodeBudget / bytesPerStoredFrame);
    targetDimensions = {
      width: Math.max(1, Math.floor(targetDimensions.width * memoryScale)),
      height: Math.max(1, Math.floor(targetDimensions.height * memoryScale))
    };
    bytesPerStoredFrame = getEstimatedBitmapByteLength(
      targetDimensions.width,
      targetDimensions.height
    );
  }
  const maximumStoredFrames = singleFrameMode
    ? 1
    : Math.max(
        1,
        Math.floor(availableDecodeBudget / Math.max(1, bytesPerStoredFrame))
      );
  let targetFrameIntervalMs = Math.max(
    MIN_GIF_FRAME_DELAY_MS,
    finiteNumber(options.frameIntervalMs, MIN_GIF_FRAME_DELAY_MS)
  );
  let estimatedStoredFrameCount = singleFrameMode
    ? 1
    : estimateStoredGifFrameCount(
        frameDurations,
        targetFrameIntervalMs,
        imageFrames.length
      );
  if (!singleFrameMode && estimatedStoredFrameCount > maximumStoredFrames) {
    targetFrameIntervalMs = Math.max(
      targetFrameIntervalMs,
      Math.ceil(totalSourceDurationMs / Math.max(1, maximumStoredFrames))
    );
    estimatedStoredFrameCount = estimateStoredGifFrameCount(
      frameDurations,
      targetFrameIntervalMs,
      maximumStoredFrames
    );
  }
  const estimatedBitmapBytes = getEstimatedBitmapSeriesByteLength(
    targetDimensions.width,
    targetDimensions.height,
    Math.max(1, estimatedStoredFrameCount)
  );
  const reservedBytes = reserveDecodedBitmapBytes(cancellationJob, estimatedBitmapBytes, {
    phase: "gif-decode",
    transientBytes: decodeTransientBytes
  });
  let compositeCanvas = null;
  let patchCanvas = null;
  let snapshotCanvas = null;
  const frames = [];
  let completed = false;
  try {
    compositeCanvas = new OffscreenCanvas(width, height);
    patchCanvas = new OffscreenCanvas(1, 1);
    snapshotCanvas = new OffscreenCanvas(targetDimensions.width, targetDimensions.height);
    const compositeCtx = compositeCanvas.getContext("2d", { alpha: true, willReadFrequently: true });
    let patchCtx = patchCanvas.getContext("2d", { alpha: true });
    const snapshotCtx = snapshotCanvas.getContext("2d", { alpha: true });
    if (!compositeCtx || !patchCtx || !snapshotCtx) {
      throw new ExportRasterError("OFFSCREEN_2D_UNAVAILABLE", "Could not create GIF decode canvases.", {
        capability: true
      });
    }
    compositeCtx.clearRect(0, 0, width, height);
    if (logicalBackgroundColor) {
      compositeCtx.fillStyle = logicalBackgroundColor;
      compositeCtx.fillRect(0, 0, width, height);
    }
    let elapsedSinceStoredFrame = Infinity;
    for (let index = 0; index < imageFrames.length; index += 1) {
      throwIfCancelled(cancellationJob);
      const rawFrame = imageFrames[index];
      let frame;
      try {
        frame = decompressFrame(rawFrame, parsed.gct, true);
      } catch (error) {
        throw new ExportRasterError("GIF_DECODE_FAILED", `GIF frame ${index} could not be decoded.`, {
          details: { cause: error instanceof Error ? error.message : "unknown error", frameIndex: index }
        });
      }
      const dims = frame?.dims || rawFrame?.image?.descriptor || {};
      const left = Number.isFinite(Number(dims.left)) ? Number(dims.left) : 0;
      const top = Number.isFinite(Number(dims.top)) ? Number(dims.top) : 0;
      const frameWidth = Math.max(1, Number(dims.width) || width);
      const frameHeight = Math.max(1, Number(dims.height) || height);
      const disposalType = Number(frame?.disposalType) || 0;
      const restoreBeforeFrame = disposalType === 3
        ? compositeCtx.getImageData(0, 0, width, height)
        : null;

      if (frame?.patch && frame.patch.length === frameWidth * frameHeight * 4) {
        if (patchCanvas.width !== frameWidth || patchCanvas.height !== frameHeight) {
          patchCanvas.width = frameWidth;
          patchCanvas.height = frameHeight;
          patchCtx = patchCanvas.getContext("2d", { alpha: true });
          if (!patchCtx) {
            throw new ExportRasterError("OFFSCREEN_2D_UNAVAILABLE", "Could not resize the GIF patch canvas.", {
              capability: true
            });
          }
        }
        patchCtx.clearRect(0, 0, frameWidth, frameHeight);
        const patchPixels = frame.patch instanceof Uint8ClampedArray
          ? frame.patch
          : new Uint8ClampedArray(frame.patch);
        patchCtx.putImageData(new ImageData(patchPixels, frameWidth, frameHeight), 0, 0);
        compositeCtx.drawImage(patchCanvas, left, top);
      }

      const frameDelayMs = frameDurations[index];
      const isLastFrame = index === imageFrames.length - 1;
      const shouldStoreFrame = singleFrameMode
        ? index === singleFrameIndex
        : index === 0 ||
          (isLastFrame && frames.length < maximumStoredFrames) ||
          (
            elapsedSinceStoredFrame >= targetFrameIntervalMs &&
            frames.length < maximumStoredFrames - 1
          );
      if (shouldStoreFrame) {
        snapshotCtx.setTransform(1, 0, 0, 1, 0, 0);
        snapshotCtx.globalAlpha = 1;
        snapshotCtx.globalCompositeOperation = "copy";
        snapshotCtx.clearRect(0, 0, targetDimensions.width, targetDimensions.height);
        snapshotCtx.imageSmoothingEnabled = options.imageSmoothing !== false;
        snapshotCtx.drawImage(
          compositeCanvas,
          0,
          0,
          width,
          height,
          0,
          0,
          targetDimensions.width,
          targetDimensions.height
        );
        snapshotCtx.globalCompositeOperation = "source-over";
        const bitmap = await createImageBitmap(snapshotCanvas);
        frames.push({
          bitmap,
          durationMs: singleFrameMode ? totalSourceDurationMs : frameDelayMs
        });
        elapsedSinceStoredFrame = frameDelayMs;
        if (singleFrameMode) {
          break;
        }
      } else if (!singleFrameMode) {
        frames[frames.length - 1].durationMs += frameDelayMs;
        elapsedSinceStoredFrame += frameDelayMs;
      }

      if (disposalType === 2) {
        if (logicalBackgroundColor) {
          compositeCtx.fillStyle = logicalBackgroundColor;
          compositeCtx.fillRect(left, top, frameWidth, frameHeight);
        } else {
          compositeCtx.clearRect(left, top, frameWidth, frameHeight);
        }
      } else if (disposalType === 3 && restoreBeforeFrame) {
        compositeCtx.putImageData(restoreBeforeFrame, 0, 0);
      }
      if (index > 0 && index % 16 === 0) {
        await yieldToWorker(cancellationJob);
      }
    }
    completed = true;
  } catch (error) {
    for (const frame of frames) {
      frame.bitmap.close?.();
    }
    throw error;
  } finally {
    if (compositeCanvas) {
      compositeCanvas.width = 1;
      compositeCanvas.height = 1;
    }
    if (patchCanvas) {
      patchCanvas.width = 1;
      patchCanvas.height = 1;
    }
    if (snapshotCanvas) {
      snapshotCanvas.width = 1;
      snapshotCanvas.height = 1;
    }
    if (!completed) {
      releaseDecodedBitmapBytes(cancellationJob, reservedBytes);
    }
  }
  const actualBitmapBytes = getEstimatedBitmapSeriesByteLength(
    targetDimensions.width,
    targetDimensions.height,
    frames.length
  );
  if (actualBitmapBytes > reservedBytes) {
    try {
      reserveDecodedBitmapBytes(cancellationJob, actualBitmapBytes - reservedBytes, {
        phase: "gif-decode-dimensions"
      });
    } catch (error) {
      for (const frame of frames) {
        frame.bitmap.close?.();
      }
      releaseDecodedBitmapBytes(cancellationJob, reservedBytes);
      throw error;
    }
  } else if (actualBitmapBytes < reservedBytes) {
    releaseDecodedBitmapBytes(cancellationJob, reservedBytes - actualBitmapBytes);
  }
  const totalDurationMs = frames.reduce((sum, frame) => sum + frame.durationMs, 0) || DEFAULT_GIF_FRAME_DELAY_MS;
  return {
    kind: "gif",
    width,
    height,
    frames,
    totalDurationMs,
    estimatedBitmapBytes: actualBitmapBytes,
    originalFrameCount: imageFrames.length,
    targetWidth: targetDimensions.width,
    targetHeight: targetDimensions.height,
    targetFrameIntervalMs
  };
}

async function createStaticBitmapAtTarget(blob, dimensions, targetDimensions, descriptor, job) {
  const needsResize =
    targetDimensions.width < dimensions.width ||
    targetDimensions.height < dimensions.height;
  if (!needsResize) {
    return createImageBitmap(blob);
  }
  try {
    return await createImageBitmap(
      blob,
      0,
      0,
      dimensions.width,
      dimensions.height,
      {
        resizeWidth: targetDimensions.width,
        resizeHeight: targetDimensions.height,
        resizeQuality: descriptor.imageSmoothing === false ? "pixelated" : "high"
      }
    );
  } catch (resizeError) {
    const sourceBitmapBytes = getEstimatedBitmapByteLength(
      dimensions.width,
      dimensions.height
    );
    const resizeCanvasBytes = getEstimatedBitmapByteLength(
      targetDimensions.width,
      targetDimensions.height
    );
    assertJobMemoryBudget(job, {
      phase: "static-resize-fallback",
      transientBytes: sourceBitmapBytes + resizeCanvasBytes + blob.size * 2
    });
    let sourceBitmap = null;
    let resizeCanvas = null;
    try {
      sourceBitmap = await createImageBitmap(blob);
      resizeCanvas = new OffscreenCanvas(targetDimensions.width, targetDimensions.height);
      const resizeContext = resizeCanvas.getContext("2d", { alpha: true });
      if (!resizeContext) {
        throw new ExportRasterError(
          "OFFSCREEN_2D_UNAVAILABLE",
          `Asset ${descriptor.id} could not create a resize canvas.`,
          { capability: true }
        );
      }
      resizeContext.imageSmoothingEnabled = descriptor.imageSmoothing !== false;
      resizeContext.drawImage(
        sourceBitmap,
        0,
        0,
        sourceBitmap.width,
        sourceBitmap.height,
        0,
        0,
        targetDimensions.width,
        targetDimensions.height
      );
      return await createImageBitmap(resizeCanvas);
    } catch (fallbackError) {
      if (fallbackError instanceof ExportRasterError) {
        throw fallbackError;
      }
      throw new ExportRasterError(
        "STATIC_RESIZE_UNAVAILABLE",
        `Asset ${descriptor.id} could not be resized in this worker.`,
        {
          capability: true,
          details: {
            resizeCause: resizeError instanceof Error ? resizeError.message : "unknown error",
            fallbackCause: fallbackError instanceof Error ? fallbackError.message : "unknown error"
          }
        }
      );
    } finally {
      sourceBitmap?.close?.();
      if (resizeCanvas) {
        resizeCanvas.width = 1;
        resizeCanvas.height = 1;
      }
    }
  }
}

async function decodeAsset(descriptor, job) {
  const providedFrames = normalizeProvidedFrames(descriptor, job);
  if (providedFrames) {
    return providedFrames;
  }
  if (descriptor.bitmap) {
    const bitmap = descriptor.bitmap;
    if (!Number.isFinite(Number(bitmap.width)) || !Number.isFinite(Number(bitmap.height))) {
      throw new ExportRasterError("INVALID_ASSET_BITMAP", `Asset ${descriptor.id} bitmap is invalid.`);
    }
    const estimatedBitmapBytes = getEstimatedBitmapByteLength(bitmap.width, bitmap.height);
    let reservedBytes = 0;
    try {
      reservedBytes = reserveDecodedBitmapBytes(job, estimatedBitmapBytes, {
        phase: "provided-bitmap"
      });
      ownBitmap(job, bitmap, descriptor.workerOwnsBitmap !== false);
    } catch (error) {
      if (descriptor.workerOwnsBitmap !== false) {
        bitmap.close?.();
      }
      releaseDecodedBitmapBytes(job, reservedBytes);
      throw error;
    }
    return {
      id: descriptor.id,
      kind: "static",
      width: Math.max(1, Math.round(bitmap.width)),
      height: Math.max(1, Math.round(bitmap.height)),
      frames: [{ bitmap, durationMs: 0 }],
      totalDurationMs: 0,
      estimatedBitmapBytes
    };
  }
  const { bytes, mimeType } = await readAssetBytes(descriptor, job);
  throwIfCancelled(job);
  const shouldDecodeGif = descriptor.kind === "gif" || (descriptor.kind !== "static" && hasGifSignature(bytes));
  if (shouldDecodeGif) {
    const decoded = await decodeGifBytes(bytes, job, descriptor);
    decoded.id = descriptor.id;
    for (const frame of decoded.frames) {
      ownBitmap(job, frame.bitmap);
    }
    return decoded;
  }
  const dimensions = sniffStaticRasterDimensions(bytes);
  if (!dimensions) {
    throw new ExportRasterError(
      "STATIC_DIMENSIONS_UNAVAILABLE",
      `Asset ${descriptor.id} dimensions could not be verified before decode.`,
      {
        capability: true,
        details: { mimeType: mimeType || descriptor.mimeType || "", sourceUrl: descriptor.url || "" }
      }
    );
  }
  const targetDimensions = getDecodeTargetDimensions(
    dimensions.width,
    dimensions.height,
    descriptor
  );
  let reservedBytes = reserveDecodedBitmapBytes(
    job,
    getEstimatedBitmapByteLength(targetDimensions.width, targetDimensions.height),
    { phase: "static-decode", transientBytes: bytes.byteLength * 2 }
  );
  let bitmap;
  try {
    const blob = new Blob([bytes], { type: mimeType || descriptor.mimeType || "" });
    bitmap = await createStaticBitmapAtTarget(
      blob,
      dimensions,
      targetDimensions,
      descriptor,
      job
    );
  } catch (error) {
    releaseDecodedBitmapBytes(job, reservedBytes);
    if (error instanceof ExportRasterError) {
      throw error;
    }
    throw new ExportRasterError("STATIC_IMAGE_DECODE_FAILED", `Asset ${descriptor.id} could not be decoded.`, {
      details: { cause: error instanceof Error ? error.message : "unknown error" }
    });
  }
  const actualBitmapBytes = getEstimatedBitmapByteLength(bitmap.width, bitmap.height);
  try {
    if (actualBitmapBytes > reservedBytes) {
      reserveDecodedBitmapBytes(job, actualBitmapBytes - reservedBytes, {
        phase: "static-decode-dimensions",
        transientBytes: bytes.byteLength * 2
      });
    } else if (actualBitmapBytes < reservedBytes) {
      releaseDecodedBitmapBytes(job, reservedBytes - actualBitmapBytes);
    }
    reservedBytes = actualBitmapBytes;
    ownBitmap(job, bitmap);
  } catch (error) {
    bitmap.close?.();
    releaseDecodedBitmapBytes(job, reservedBytes);
    throw error;
  }
  return {
    id: descriptor.id,
    kind: "static",
    width: Math.max(1, Math.round(dimensions.width)),
    height: Math.max(1, Math.round(dimensions.height)),
    frames: [{ bitmap, durationMs: 0 }],
    totalDurationMs: 0,
    estimatedBitmapBytes: actualBitmapBytes,
    targetWidth: Math.max(1, Math.round(bitmap.width)),
    targetHeight: Math.max(1, Math.round(bitmap.height))
  };
}

function resolveAssetFrame(asset, timeMs, phaseOffsetMs = 0, playbackRate = 1) {
  if (!asset || !asset.frames.length) {
    return null;
  }
  if (asset.frames.length === 1 || asset.totalDurationMs <= 0 || playbackRate <= 0) {
    return asset.frames[0].bitmap;
  }
  const duration = Math.max(1, asset.totalDurationMs);
  let wrapped = (finiteNumber(timeMs, 0) * playbackRate + phaseOffsetMs) % duration;
  if (wrapped < 0) {
    wrapped += duration;
  }
  let elapsed = 0;
  for (const frame of asset.frames) {
    elapsed += Math.max(MIN_GIF_FRAME_DELAY_MS, finiteNumber(frame.durationMs, DEFAULT_GIF_FRAME_DELAY_MS));
    if (wrapped < elapsed) {
      return frame.bitmap;
    }
  }
  return asset.frames[asset.frames.length - 1].bitmap;
}

function resetContext(context) {
  context.setTransform(1, 0, 0, 1, 0, 0);
  context.globalAlpha = 1;
  context.globalCompositeOperation = "source-over";
  context.imageSmoothingEnabled = true;
  if ("filter" in context) {
    context.filter = "none";
  }
}

function resizeCanvas(canvas, width, height) {
  if (canvas.width !== width) {
    canvas.width = width;
  }
  if (canvas.height !== height) {
    canvas.height = height;
  }
}

function ensureScratch(job, name, width, height, options = {}) {
  const safeWidth = Math.max(1, Math.ceil(Number(width) || 1));
  const safeHeight = Math.max(1, Math.ceil(Number(height) || 1));
  const nextByteLength = getSafeRgbaByteLength(safeWidth, safeHeight);
  if (!job.scratch[name]) {
    assertJobMemoryBudget(job, {
      phase: `${name}-canvas`,
      additionalCanvasBytes: nextByteLength
    });
    const canvas = new OffscreenCanvas(safeWidth, safeHeight);
    const context = canvas.getContext("2d", { alpha: true, ...options });
    if (!context) {
      canvas.width = 1;
      canvas.height = 1;
      throw new ExportRasterError("OFFSCREEN_2D_UNAVAILABLE", `Could not create the ${name} canvas.`, {
        capability: true
      });
    }
    job.canvasBytes += nextByteLength;
    job.scratch[name] = { canvas, context, reservedBytes: nextByteLength };
  }
  const target = job.scratch[name];
  const additionalCanvasBytes = Math.max(0, nextByteLength - (target.reservedBytes || 0));
  if (additionalCanvasBytes > 0) {
    assertJobMemoryBudget(job, {
      phase: `${name}-canvas-resize`,
      additionalCanvasBytes
    });
  }
  resizeCanvas(target.canvas, safeWidth, safeHeight);
  if (additionalCanvasBytes > 0) {
    target.reservedBytes += additionalCanvasBytes;
    job.canvasBytes += additionalCanvasBytes;
  }
  resetContext(target.context);
  target.context.clearRect(0, 0, target.canvas.width, target.canvas.height);
  return target;
}

function applyColorMatrix(job, context, width, height, matrix) {
  if (!matrix) {
    return;
  }
  assertJobMemoryBudget(job, {
    phase: "color-matrix-readback",
    transientBytes: getSafeRgbaByteLength(width, height)
  });
  const image = context.getImageData(0, 0, width, height);
  const data = image.data;
  for (let index = 0; index < data.length; index += 4) {
    const red = data[index] / 255;
    const green = data[index + 1] / 255;
    const blue = data[index + 2] / 255;
    const alpha = data[index + 3] / 255;
    data[index] = clamp(Math.round((matrix[0] * red + matrix[1] * green + matrix[2] * blue + matrix[3] * alpha + matrix[4]) * 255), 0, 255);
    data[index + 1] = clamp(Math.round((matrix[5] * red + matrix[6] * green + matrix[7] * blue + matrix[8] * alpha + matrix[9]) * 255), 0, 255);
    data[index + 2] = clamp(Math.round((matrix[10] * red + matrix[11] * green + matrix[12] * blue + matrix[13] * alpha + matrix[14]) * 255), 0, 255);
    data[index + 3] = clamp(Math.round((matrix[15] * red + matrix[16] * green + matrix[17] * blue + matrix[18] * alpha + matrix[19]) * 255), 0, 255);
  }
  context.putImageData(image, 0, 0);
}

function applyPixelation(job, context, width, height, pixelSize) {
  const blockSize = clamp(Math.round(pixelSize), 1, 64);
  if (blockSize <= 1 || width <= 1 || height <= 1) {
    return;
  }
  const reducedWidth = Math.max(1, Math.ceil(width / blockSize));
  const reducedHeight = Math.max(1, Math.ceil(height / blockSize));
  const reduced = ensureScratch(job, "pixel", reducedWidth, reducedHeight, { willReadFrequently: true });
  assertJobMemoryBudget(job, {
    phase: "pixelate-readback",
    transientBytes:
      getSafeRgbaByteLength(width, height) +
      getSafeRgbaByteLength(reducedWidth, reducedHeight)
  });
  const sourceData = context.getImageData(0, 0, width, height).data;
  const reducedImage = reduced.context.createImageData(reducedWidth, reducedHeight);
  const targetData = reducedImage.data;
  for (let y = 0; y < reducedHeight; y += 1) {
    const sampleY = Math.min(height - 1, Math.floor(y * blockSize + blockSize / 2));
    for (let x = 0; x < reducedWidth; x += 1) {
      const sampleX = Math.min(width - 1, Math.floor(x * blockSize + blockSize / 2));
      const sourceOffset = (sampleY * width + sampleX) * 4;
      const targetOffset = (y * reducedWidth + x) * 4;
      targetData[targetOffset] = sourceData[sourceOffset];
      targetData[targetOffset + 1] = sourceData[sourceOffset + 1];
      targetData[targetOffset + 2] = sourceData[sourceOffset + 2];
      targetData[targetOffset + 3] = sourceData[sourceOffset + 3];
    }
  }
  reduced.context.putImageData(reducedImage, 0, 0);
  resetContext(context);
  context.clearRect(0, 0, width, height);
  context.imageSmoothingEnabled = false;
  context.drawImage(reduced.canvas, 0, 0, reducedWidth, reducedHeight, 0, 0, width, height);
}

function drawSourceWithEffects(job, context, source, drawWidth, drawHeight, entry) {
  if (!entry.tintLayers.length && !entry.colorMatrix && entry.pixelateAmount <= 0 && entry.blurAmount <= 0) {
    context.drawImage(source, -drawWidth / 2, -drawHeight / 2, drawWidth, drawHeight);
    return;
  }
  const scratchWidth = Math.max(1, Math.ceil(drawWidth));
  const scratchHeight = Math.max(1, Math.ceil(drawHeight));
  const scratch = ensureScratch(job, "tint", scratchWidth, scratchHeight, { willReadFrequently: true });
  scratch.context.imageSmoothingEnabled = entry.imageRendering === "auto";
  scratch.context.drawImage(source, 0, 0, scratchWidth, scratchHeight);
  for (const layer of entry.tintLayers) {
    scratch.context.globalCompositeOperation = "source-atop";
    scratch.context.globalAlpha = layer.amountPercent / 100;
    scratch.context.fillStyle = layer.color;
    scratch.context.fillRect(0, 0, scratchWidth, scratchHeight);
  }
  scratch.context.globalAlpha = 1;
  scratch.context.globalCompositeOperation = "source-over";
  applyColorMatrix(job, scratch.context, scratchWidth, scratchHeight, entry.colorMatrix);
  if (entry.pixelateAmount > 0) {
    applyPixelation(job, scratch.context, scratchWidth, scratchHeight, entry.pixelateAmount);
  }
  context.save();
  if (entry.blurAmount > 0) {
    if (!("filter" in context)) {
      throw new ExportRasterError(
        "BLUR_FILTER_UNAVAILABLE",
        "This browser cannot apply Canvas2D blur in an export worker.",
        { capability: true }
      );
    }
    context.filter = `blur(${entry.blurAmount.toFixed(2)}px)`;
  }
  context.imageSmoothingEnabled = entry.pixelateAmount > 0 ? false : entry.imageRendering === "auto";
  context.drawImage(scratch.canvas, -drawWidth / 2, -drawHeight / 2, drawWidth, drawHeight);
  context.restore();
}

function drawStamp(job, context, scene, entry, timeMs, scaleX, scaleY) {
  const asset = job.assets.get(entry.sourceId);
  if (!asset) {
    throw new ExportRasterError("ASSET_NOT_PREPARED", `Asset ${entry.sourceId} was not prepared.`);
  }
  const source = resolveAssetFrame(asset, timeMs, entry.phaseOffsetMs, entry.playbackRate);
  if (!source) {
    throw new ExportRasterError("ASSET_NOT_PREPARED", `Asset ${entry.sourceId} has no renderable frame.`);
  }
  const bounds = scene.selectionBounds;
  const drawWidth = entry.width * scaleX;
  const drawHeight = entry.height * scaleY;
  const centerX = (entry.centerX - bounds.left) * scaleX;
  const centerY = (entry.centerY - bounds.top) * scaleY;
  context.save();
  context.globalAlpha = entry.opacity;
  const operation = entry.blendMode === "normal" ? "source-over" : entry.blendMode;
  if (!job.capabilities?.blendModes?.includes(entry.blendMode)) {
    context.restore();
    throw new ExportRasterError(
      "UNSUPPORTED_BLEND_MODE",
      `This worker cannot reproduce blend mode ${entry.blendMode}.`,
      { capability: true }
    );
  }
  context.globalCompositeOperation = operation;
  if (context.globalCompositeOperation !== operation) {
    context.restore();
    throw new ExportRasterError(
      "UNSUPPORTED_BLEND_MODE",
      `This worker rejected blend mode ${entry.blendMode}.`,
      { capability: true }
    );
  }
  context.imageSmoothingEnabled = entry.imageRendering === "auto";
  context.translate(centerX, centerY);
  context.rotate((entry.rotation * Math.PI) / 180);
  drawSourceWithEffects(job, context, source, drawWidth, drawHeight, entry);
  context.restore();
}

function drawBackground(job, context, scene, background, timeMs) {
  resetContext(context);
  context.clearRect(0, 0, scene.outputWidth, scene.outputHeight);
  if (background.include || background.matteColor) {
    context.fillStyle = background.include ? background.color : background.matteColor;
    context.fillRect(0, 0, scene.outputWidth, scene.outputHeight);
  }
  if (!background.image || background.image.opacity <= 0) {
    return;
  }
  const asset = job.assets.get(background.image.sourceId);
  if (!asset) {
    throw new ExportRasterError("ASSET_NOT_PREPARED", `Background asset ${background.image.sourceId} was not prepared.`);
  }
  const image = resolveAssetFrame(
    asset,
    timeMs,
    background.image.phaseOffsetMs,
    background.image.playbackRate
  );
  if (!image) {
    return;
  }
  context.save();
  context.globalAlpha = background.image.opacity;
  context.imageSmoothingEnabled = true;
  if (background.image.mode === "tile") {
    const selectionWidth = Math.max(1, scene.selectionBounds.right - scene.selectionBounds.left);
    const scaleX = scene.outputWidth / selectionWidth;
    const tileWidth = Math.max(1, background.image.tileSize * scaleX);
    const tileHeight = Math.max(1, tileWidth * (asset.height / Math.max(1, asset.width)));
    const startX = -(scene.outputWidth % tileWidth) / 2;
    const startY = -(scene.outputHeight % tileHeight) / 2;
    for (let y = startY; y < scene.outputHeight; y += tileHeight) {
      for (let x = startX; x < scene.outputWidth; x += tileWidth) {
        context.drawImage(image, x, y, tileWidth, tileHeight);
      }
    }
  } else {
    const scale = Math.max(scene.outputWidth / asset.width, scene.outputHeight / asset.height);
    const drawWidth = asset.width * scale;
    const drawHeight = asset.height * scale;
    context.drawImage(
      image,
      (scene.outputWidth - drawWidth) / 2,
      (scene.outputHeight - drawHeight) / 2,
      drawWidth,
      drawHeight
    );
  }
  context.restore();
}

function validatePreparedSources(job, entries, background) {
  for (const entry of entries) {
    if (!job.assets.has(entry.sourceId)) {
      throw new ExportRasterError("ASSET_NOT_PREPARED", `Asset ${entry.sourceId} was not declared during prepare.`);
    }
  }
  if (background.image && !job.assets.has(background.image.sourceId)) {
    throw new ExportRasterError(
      "ASSET_NOT_PREPARED",
      `Background asset ${background.image.sourceId} was not declared during prepare.`
    );
  }
}

async function rasterizeFrame(job, frame = {}, progress = null) {
  throwIfCancelled(job);
  const scene = job.scene;
  const entries = Array.isArray(frame.entries)
    ? frame.entries.map((entry, index) => normalizeEntry(entry, index))
    : scene.entries;
  const background = frame.background
    ? normalizeBackground(frame.background, scene.background)
    : scene.background;
  validatePreparedSources(job, entries, background);
  const output = ensureScratch(job, "output", scene.outputWidth, scene.outputHeight, { willReadFrequently: true });
  const artwork = ensureScratch(job, "artwork", scene.outputWidth, scene.outputHeight);
  const selectionWidth = Math.max(1, scene.selectionBounds.right - scene.selectionBounds.left);
  const selectionHeight = Math.max(1, scene.selectionBounds.bottom - scene.selectionBounds.top);
  const scaleX = scene.outputWidth / selectionWidth;
  const scaleY = scene.outputHeight / selectionHeight;
  const timeMs = finiteNumber(frame.timeMs, 0);

  for (let index = 0; index < entries.length; index += 1) {
    throwIfCancelled(job);
    drawStamp(job, artwork.context, scene, entries[index], timeMs, scaleX, scaleY);
    if (index > 0 && index % STAMP_YIELD_INTERVAL === 0) {
      progress?.((index + 1) / Math.max(1, entries.length));
      await yieldToWorker(job);
    }
  }
  progress?.(1);
  drawBackground(job, output.context, scene, background, timeMs);
  output.context.save();
  output.context.globalAlpha = 1;
  output.context.globalCompositeOperation = "source-over";
  output.context.drawImage(artwork.canvas, 0, 0);
  output.context.restore();
  return { canvas: output.canvas, context: output.context, timeMs };
}

async function encodeFrameResult(job, frame, outputKind, progress = null) {
  const rendered = await rasterizeFrame(job, frame, progress);
  throwIfCancelled(job);
  const width = job.scene.outputWidth;
  const height = job.scene.outputHeight;
  const frameByteLength = getSafeRgbaByteLength(width, height);
  if (outputKind === "rgba") {
    assertJobMemoryBudget(job, {
      phase: "rgba-readback",
      transientBytes: frameByteLength
    });
    const image = rendered.context.getImageData(0, 0, width, height);
    return {
      payload: {
        kind: "rgba",
        width,
        height,
        timeMs: rendered.timeMs,
        buffer: image.data.buffer
      },
      transfer: [image.data.buffer]
    };
  }
  if (outputKind === "bitmap") {
    assertJobMemoryBudget(job, {
      phase: "bitmap-transfer",
      transientBytes: frameByteLength
    });
    let bitmap;
    if (typeof rendered.canvas.transferToImageBitmap === "function") {
      bitmap = rendered.canvas.transferToImageBitmap();
    } else if (typeof createImageBitmap === "function") {
      bitmap = await createImageBitmap(rendered.canvas);
    } else {
      throw new ExportRasterError("BITMAP_OUTPUT_UNAVAILABLE", "ImageBitmap output is unavailable.", {
        capability: true
      });
    }
    return {
      payload: { kind: "bitmap", width, height, timeMs: rendered.timeMs, bitmap },
      transfer: [bitmap]
    };
  }
  if (typeof rendered.canvas.convertToBlob !== "function") {
    throw new ExportRasterError("PNG_OUTPUT_UNAVAILABLE", "OffscreenCanvas PNG output is unavailable.", {
      capability: true
    });
  }
  assertJobMemoryBudget(job, {
    phase: "png-encode",
    transientBytes: frameByteLength
  });
  const blob = await rendered.canvas.convertToBlob({ type: "image/png" });
  return {
    payload: { kind: "png", width, height, timeMs: rendered.timeMs, blob },
    transfer: []
  };
}

function normalizeOutputKind(value) {
  if (value === "rgba" || value === "bitmap" || value === "png") {
    return value;
  }
  return "png";
}

function createJob(jobId, memoryBudgetBytes = null) {
  return {
    id: jobId,
    scene: null,
    assets: new Map(),
    scratch: Object.create(null),
    ownedBitmaps: new Set(),
    abortControllers: new Set(),
    memoryBudgetBytes: getDeviceAwareMemoryBudgetBytes(memoryBudgetBytes),
    decodedBitmapBytes: 0,
    canvasBytes: 0,
    outputWorkingSetReserveBytes: 0,
    queue: Promise.resolve(),
    pendingOperations: 0,
    cancelled: false,
    released: false,
    prepared: false,
    capabilities: null
  };
}

function cleanupJob(job) {
  if (job.cleaned) {
    return;
  }
  job.cleaned = true;
  for (const controller of job.abortControllers) {
    controller.abort();
  }
  job.abortControllers.clear();
  for (const bitmap of job.ownedBitmaps) {
    try {
      bitmap.close?.();
    } catch (_error) {
      // Closing an already-transferred/closed ImageBitmap is harmless cleanup.
    }
  }
  job.ownedBitmaps.clear();
  job.assets.clear();
  for (const target of Object.values(job.scratch)) {
    if (target?.canvas) {
      target.canvas.width = 1;
      target.canvas.height = 1;
    }
  }
  job.scratch = Object.create(null);
  job.decodedBitmapBytes = 0;
  job.canvasBytes = 0;
  job.outputWorkingSetReserveBytes = 0;
  job.scene = null;
}

function maybeCleanupJob(job) {
  if ((job.cancelled || job.released) && job.pendingOperations === 0) {
    cleanupJob(job);
  }
}

function retireJob(job, cancelled = false) {
  job.cancelled ||= cancelled;
  job.released = true;
  for (const controller of job.abortControllers) {
    controller.abort();
  }
  if (jobs.get(job.id) === job) {
    jobs.delete(job.id);
  }
  maybeCleanupJob(job);
}

function enqueueJobOperation(job, operation) {
  job.pendingOperations += 1;
  const result = job.queue
    .catch(() => undefined)
    .then(async () => {
      throwIfCancelled(job);
      return operation();
    });
  job.queue = result.catch(() => undefined);
  return result.finally(() => {
    job.pendingOperations -= 1;
    maybeCleanupJob(job);
  });
}

async function probeCapabilities() {
  const capabilities = {
    moduleWorker: true,
    offscreenCanvas2d: false,
    pixelReadback: false,
    gifDisposal: false,
    png: false,
    rgba: false,
    imageBitmap: false,
    canvasFilter: false,
    blendModes: [],
    memoryBudgetBytes: getDeviceAwareMemoryBudgetBytes()
  };
  if (typeof OffscreenCanvas !== "function") {
    return capabilities;
  }
  const canvas = new OffscreenCanvas(2, 2);
  const context = canvas.getContext("2d", { alpha: true, willReadFrequently: true });
  if (!context) {
    return capabilities;
  }
  capabilities.offscreenCanvas2d = true;
  context.fillStyle = "#ff0000";
  context.fillRect(0, 0, 1, 1);
  try {
    const pixel = context.getImageData(0, 0, 1, 1).data;
    capabilities.pixelReadback = pixel[0] === 255 && pixel[3] === 255;
    capabilities.rgba = capabilities.pixelReadback;
  } catch (_error) {
    capabilities.pixelReadback = false;
  }
  for (const mode of BLEND_MODES) {
    const operation = mode === "normal" ? "source-over" : mode;
    context.globalCompositeOperation = "source-over";
    context.globalCompositeOperation = operation;
    if (context.globalCompositeOperation === operation) {
      capabilities.blendModes.push(mode);
    }
  }
  context.globalCompositeOperation = "source-over";
  if ("filter" in context) {
    try {
      context.filter = "blur(1px)";
      capabilities.canvasFilter = context.filter === "blur(1px)";
      context.filter = "none";
    } catch (_error) {
      capabilities.canvasFilter = false;
    }
  }
  if (typeof canvas.convertToBlob === "function") {
    try {
      const blob = await canvas.convertToBlob({ type: "image/png" });
      capabilities.png = blob?.type === "image/png";
    } catch (_error) {
      capabilities.png = false;
    }
  }
  let canvasImageBitmapSupported = false;
  if (typeof createImageBitmap === "function") {
    let probeBitmap = null;
    try {
      probeBitmap = await createImageBitmap(canvas);
      canvasImageBitmapSupported = Boolean(probeBitmap);
    } catch (_error) {
      canvasImageBitmapSupported = false;
    } finally {
      probeBitmap?.close?.();
    }
  }
  capabilities.imageBitmap =
    typeof canvas.transferToImageBitmap === "function" || canvasImageBitmapSupported;
  capabilities.gifDisposal = canvasImageBitmapSupported && capabilities.pixelReadback;
  canvas.width = 1;
  canvas.height = 1;
  return capabilities;
}

const capabilitiesPromise = probeCapabilities();

async function handlePrepare(message) {
  const jobId = normalizeJobId(message.jobId);
  const previous = jobs.get(jobId);
  if (previous) {
    retireJob(previous, true);
  }
  const capabilities = await capabilitiesPromise;
  if (!capabilities.offscreenCanvas2d || !capabilities.gifDisposal) {
    throw new ExportRasterError(
      "WORKER_RASTER_UNAVAILABLE",
      "This browser does not provide the OffscreenCanvas features needed for worker export.",
      { capability: true, details: { capabilities } }
    );
  }
  const requestedMemoryBudget = message.options?.memoryBudgetBytes ?? message.scene?.memoryBudgetBytes;
  const job = createJob(jobId, requestedMemoryBudget);
  job.capabilities = capabilities;
  jobs.set(jobId, job);
  try {
    await enqueueJobOperation(job, async () => {
      job.scene = normalizeScene(message.scene);
      // Peak frame production retains the output and artwork canvases plus
      // one encoder/readback/transfer-sized allocation.
      job.outputWorkingSetReserveBytes = getSafeRgbaByteLength(
        job.scene.outputWidth,
        job.scene.outputHeight,
        3
      );
      assertJobMemoryBudget(job, { phase: "output-working-set" });
      const rawAssets = Array.isArray(message.assets) ? message.assets : message.scene?.assets;
      const descriptors = collectAssetDescriptors(job.scene, rawAssets);
      let completed = 0;
      let cursor = 0;
      const descriptorList = Array.from(descriptors.values());
      const decodeNext = async () => {
        while (cursor < descriptorList.length) {
          throwIfCancelled(job);
          const descriptor = descriptorList[cursor];
          cursor += 1;
          if (!(descriptor.decodeBudgetBytes > 0)) {
            const remainingAssetCount = Math.max(1, descriptorList.length - cursor + 1);
            descriptor.decodeBudgetBytes = Math.max(
              MIN_BITMAP_ALLOCATION_BYTES,
              Math.floor(getAvailableDecodedBytes(job) / remainingAssetCount)
            );
          }
          const asset = await decodeAsset(descriptor, job);
          throwIfCancelled(job);
          job.assets.set(descriptor.id, asset);
          completed += 1;
          post("progress", {
            action: "prepare",
            jobId,
            ...(getRequestId(message) != null ? { requestId: getRequestId(message) } : {}),
            phase: "assets",
            completed,
            total: descriptors.size
          });
          await yieldToWorker(job);
        }
      };
      // Decoding two animated sources concurrently doubles their composite,
      // patch, restore, and createImageBitmap peak. Serial preparation keeps
      // the budget deterministic without changing any decoded frame.
      const decodeConcurrency = 1;
      await Promise.all(Array.from({ length: decodeConcurrency }, decodeNext));
      validatePreparedSources(job, job.scene.entries, job.scene.background);
      job.prepared = true;
    });
  } catch (error) {
    retireJob(job, true);
    throw error;
  }
  post("prepared", {
    action: "prepare",
    jobId,
    ...(getRequestId(message) != null ? { requestId: getRequestId(message) } : {}),
    scene: {
      outputWidth: job.scene.outputWidth,
      outputHeight: job.scene.outputHeight,
      stampCount: job.scene.entries.length
    },
    assets: Array.from(job.assets.values(), (asset) => ({
      id: asset.id,
      kind: asset.kind,
      width: asset.width,
      height: asset.height,
      frameCount: asset.frames.length,
      durations: asset.frames.map((frame) => frame.durationMs),
      totalDurationMs: asset.totalDurationMs,
      estimatedBitmapBytes: asset.estimatedBitmapBytes || 0
    })),
    memory: {
      budgetBytes: job.memoryBudgetBytes,
      decodedBitmapBytes: job.decodedBitmapBytes,
      reservedOutputWorkingSetBytes: job.outputWorkingSetReserveBytes
    }
  });
}

function requirePreparedJob(message) {
  const jobId = normalizeJobId(message.jobId);
  const job = jobs.get(jobId);
  if (!job || job.released || job.cancelled) {
    throw new ExportRasterError("JOB_NOT_FOUND", `Export raster job ${jobId} is not available.`);
  }
  return job;
}

async function handleRenderFrame(message) {
  const job = requirePreparedJob(message);
  const requestId = getRequestId(message);
  const outputKind = normalizeOutputKind(message.output);
  const frame = {
    timeMs: message.timeMs,
    entries: message.entries,
    background: message.background
  };
  const result = await enqueueJobOperation(job, async () => {
    if (!job.prepared) {
      throw new ExportRasterError("JOB_NOT_PREPARED", `Export raster job ${job.id} is not prepared.`);
    }
    return encodeFrameResult(job, frame, outputKind, (fraction) => {
      post("progress", {
        action: "render-frame",
        jobId: job.id,
        ...(requestId != null ? { requestId } : {}),
        phase: "stamps",
        fraction
      });
    });
  });
  post(
    "rendered",
    {
      action: "render-frame",
      jobId: job.id,
      ...(requestId != null ? { requestId } : {}),
      output: result.payload
    },
    result.transfer
  );
}

async function handleRenderFrames(message) {
  const job = requirePreparedJob(message);
  const requestId = getRequestId(message);
  if (!Array.isArray(message.frames) || message.frames.length === 0 || message.frames.length > FRAME_LIMIT) {
    throw new ExportRasterError("INVALID_FRAME_LIST", `frames must contain between 1 and ${FRAME_LIMIT} items.`);
  }
  const outputKind = normalizeOutputKind(message.output);
  const batch = await enqueueJobOperation(job, async () => {
    if (!job.prepared) {
      throw new ExportRasterError("JOB_NOT_PREPARED", `Export raster job ${job.id} is not prepared.`);
    }
    const frameByteLength = getSafeRgbaByteLength(
      job.scene.outputWidth,
      job.scene.outputHeight
    );
    let retainedOutputReserveBytes = 0;
    const collected = [];
    try {
      retainedOutputReserveBytes = reserveDecodedBitmapBytes(
        job,
        frameByteLength * Math.max(0, message.frames.length - 1),
        { phase: "render-frames-batch" }
      );
      for (let index = 0; index < message.frames.length; index += 1) {
        throwIfCancelled(job);
        const result = await encodeFrameResult(job, message.frames[index] || {}, outputKind);
        collected.push(result);
        post("progress", {
          action: "render-frames",
          jobId: job.id,
          ...(requestId != null ? { requestId } : {}),
          phase: "frames",
          completed: index + 1,
          total: message.frames.length
        });
        await yieldToWorker(job);
      }
    } catch (error) {
      for (const result of collected) {
        if (result.payload?.kind === "bitmap") {
          result.payload.bitmap?.close?.();
        }
      }
      releaseDecodedBitmapBytes(job, retainedOutputReserveBytes);
      throw error;
    }
    return { results: collected, retainedOutputReserveBytes };
  });
  const results = batch.results;
  const transfer = results.flatMap((result) => result.transfer);
  try {
    post(
      "frames-rendered",
      {
        action: "render-frames",
        jobId: job.id,
        ...(requestId != null ? { requestId } : {}),
        outputs: results.map((result) => result.payload)
      },
      transfer
    );
  } catch (error) {
    for (const result of results) {
      if (result.payload?.kind === "bitmap") {
        result.payload.bitmap?.close?.();
      }
    }
    throw error;
  } finally {
    releaseDecodedBitmapBytes(job, batch.retainedOutputReserveBytes);
  }
}

function handleCancel(message, release = false) {
  const jobId = normalizeJobId(message.jobId);
  const job = jobs.get(jobId);
  if (job) {
    retireJob(job, true);
  }
  post(release ? "released" : "cancelled", {
    action: release ? "release" : "cancel",
    jobId,
    ...(getRequestId(message) != null ? { requestId: getRequestId(message) } : {}),
    active: Boolean(job)
  });
}

async function dispatchMessage(message) {
  if (message?.protocol !== EXPORT_RASTER_PROTOCOL) {
    return;
  }
  if (message.version !== EXPORT_RASTER_VERSION) {
    throw new ExportRasterError(
      "UNSUPPORTED_PROTOCOL_VERSION",
      `Protocol version ${String(message.version)} is unsupported.`,
      { capability: true, details: { supportedVersion: EXPORT_RASTER_VERSION } }
    );
  }
  switch (message.type) {
    case "probe": {
      const capabilities = await capabilitiesPromise;
      post("ready", {
        action: "probe",
        ...(getRequestId(message) != null ? { requestId: getRequestId(message) } : {}),
        capabilities
      });
      break;
    }
    case "prepare":
      await handlePrepare(message);
      break;
    case "render":
    case "render-frame":
      await handleRenderFrame(message);
      break;
    case "render-frames":
      await handleRenderFrames(message);
      break;
    case "cancel":
      handleCancel(message, false);
      break;
    case "release":
      handleCancel(message, true);
      break;
    default:
      throw new ExportRasterError("UNKNOWN_MESSAGE", `Unknown worker message type: ${String(message.type)}.`);
  }
}

workerScope?.addEventListener("message", (event) => {
  const message = event?.data;
  Promise.resolve(dispatchMessage(message)).catch((error) => {
    postError(message?.type || "unknown", error, message);
  });
});

capabilitiesPromise
  .then((capabilities) => {
    post("ready", { action: "startup", capabilities });
  })
  .catch((error) => {
    postError("startup", error);
  });
