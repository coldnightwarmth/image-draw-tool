import { decompressFrame, parseGIF } from "./gifuct-js.bundle.mjs";

// Accelerated scene renderer protocol. Instantiate with:
//   new Worker("./scene-render-worker.js", { type: "module" })
//
// Every request uses `{ protocol: "scene-render", version: 1, type, ... }`.
// See docs/scene-render-worker-protocol.md for the complete protocol and exact
// stamp record schema. This worker never intentionally substitutes a static
// first frame for an animated non-GIF source; those sources produce explicit
// capability errors so the caller can retain its DOM renderer fallback.

export const SCENE_RENDER_PROTOCOL = "scene-render";
export const SCENE_RENDER_VERSION = 1;

const DEFAULT_GIF_FRAME_DELAY_MS = 50;
const DEFAULT_MAX_SOURCE_BYTES = 128 * 1024 * 1024;
const MIN_MEMORY_BUDGET_BYTES = 64 * 1024 * 1024;
const MAX_MEMORY_BUDGET_BYTES = 1024 * 1024 * 1024;
const DEFAULT_MEMORY_BUDGET_BYTES = 256 * 1024 * 1024;
const MAX_GIF_LOGICAL_PIXELS = 64 * 1024 * 1024;
const MAX_GIF_FRAMES = 20000;
const MAX_BLUR_RADIUS = 256;
const MAX_DPR = 4;
const SOURCE_PROGRESS_INTERVAL = 64;

const DECLARED_BLEND_MODES = [
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
  "luminosity",
];

class SceneRenderError extends Error {
  constructor(
    code,
    message,
    { capability = false, retriable = false, recordId = null, sourceUrl = "", details = null } = {}
  ) {
    super(message);
    this.name = "SceneRenderError";
    this.code = code;
    this.capability = capability;
    this.retriable = retriable;
    this.recordId = recordId;
    this.sourceUrl = sourceUrl;
    this.details = details;
  }
}

class WorkQueue {
  constructor(limit) {
    this.limit = Math.max(1, Math.floor(Number(limit) || 1));
    this.active = 0;
    this.pending = [];
  }

  add(task) {
    return new Promise((resolve, reject) => {
      this.pending.push({ task, resolve, reject });
      this.pump();
    });
  }

  pump() {
    while (this.active < this.limit && this.pending.length) {
      const item = this.pending.shift();
      this.active += 1;
      Promise.resolve()
        .then(item.task)
        .then(item.resolve, item.reject)
        .finally(() => {
          this.active -= 1;
          this.pump();
        });
    }
  }
}

const workerScope = typeof self !== "undefined" ? self : null;
const sourceCache = new Map();

const renderer = {
  initialized: false,
  disposed: false,
  canvas: null,
  context: null,
  width: 1,
  height: 1,
  dpr: 1,
  camera: { x: 0, y: 0, scale: 1 },
  records: new Map(),
  order: [],
  revision: 0,
  sceneGeneration: 0,
  paused: false,
  pausedAt: 0,
  renderTimerId: null,
  renderDueAt: Infinity,
  lastDrawAt: 0,
  clientClockOffsetMs: 0,
  sourceQueue: new WorkQueue(2),
  sourceUsageCache: null,
  sourceMaintenanceTimerId: null,
  maxSourceBytes: DEFAULT_MAX_SOURCE_BYTES,
  memoryBudgetBytes: DEFAULT_MEMORY_BUDGET_BYTES,
  reservedBitmapBytes: 0,
  capabilities: null,
};

function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}

function finiteNumber(value, fallback = 0) {
  const numeric = Number(value);
  return Number.isFinite(numeric) ? numeric : fallback;
}

function finitePositive(value, fallback = 1) {
  const numeric = Number(value);
  return Number.isFinite(numeric) && numeric > 0 ? numeric : fallback;
}

export function calculateAvailableBitmapBytes(
  memoryBudgetBytes,
  canvasBytes,
  retainedBitmapBytes,
  reservedBitmapBytes
) {
  return Math.max(
    0,
    Math.floor(Math.max(0, finiteNumber(memoryBudgetBytes))) -
      Math.floor(Math.max(0, finiteNumber(canvasBytes))) -
      Math.floor(Math.max(0, finiteNumber(retainedBitmapBytes))) -
      Math.floor(Math.max(0, finiteNumber(reservedBitmapBytes)))
  );
}

export function sumReadySourceBitmapBytes(sources) {
  let total = 0;
  for (const source of sources || []) {
    if (source?.status === "ready") {
      total += Math.max(0, finiteNumber(source.data?.estimatedBitmapBytes));
    }
  }
  return total;
}

function normalizeClientTimestamp(value, fallback = performance.now()) {
  if (value == null) {
    return fallback;
  }
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) {
    return fallback;
  }
  // Also accept epoch-like DOMHighRes timestamps for callers that send
  // performance.timeOrigin + performance.now().
  if (numeric > 100000000000) {
    return numeric - performance.timeOrigin;
  }
  return numeric + renderer.clientClockOffsetMs;
}

function normalizeRevision(value, fallback = renderer.revision) {
  const numeric = Number(value);
  if (!Number.isSafeInteger(numeric) || numeric < 0) {
    throw new SceneRenderError("INVALID_REVISION", "revision must be a non-negative safe integer.");
  }
  return numeric ?? fallback;
}

function normalizeRecordId(value) {
  if (typeof value === "string" && value.length > 0) {
    return value;
  }
  if (typeof value === "number" && Number.isFinite(value)) {
    return value;
  }
  throw new SceneRenderError("INVALID_RECORD_ID", "A stamp id must be a non-empty string or finite number.");
}

function getRecordKey(id) {
  return `${typeof id}:${String(id)}`;
}

function normalizeCamera(value) {
  const candidate = value && typeof value === "object" ? value : {};
  const scale = Number(candidate.scale);
  if (!Number.isFinite(scale) || scale <= 0) {
    throw new SceneRenderError("INVALID_CAMERA", "camera.scale must be a positive finite number.");
  }
  return {
    x: finiteNumber(candidate.x, 0),
    y: finiteNumber(candidate.y, 0),
    scale,
  };
}

function hasActiveTintValue(value) {
  if (Array.isArray(value)) {
    return value.some(hasActiveTintValue);
  }
  if (!value || typeof value !== "object") {
    return false;
  }
  if (finiteNumber(value.amountPercent ?? value.amount, 0) > 0) {
    return true;
  }
  return Array.isArray(value.layers) && value.layers.some(hasActiveTintValue);
}

function normalizeFilter(record, recordId) {
  let blur = record.blurAmount ?? record.blur ?? 0;
  const filter = record.filter;
  if (typeof filter === "string") {
    const normalized = filter.trim().toLowerCase();
    if (!normalized || normalized === "none") {
      blur = 0;
    } else {
      const match = normalized.match(/^blur\(\s*([0-9]+(?:\.[0-9]+)?)px\s*\)$/);
      if (!match) {
        throw new SceneRenderError(
          "UNSUPPORTED_FILTER",
          "The accelerated renderer supports only a blur filter.",
          { capability: true, recordId }
        );
      }
      blur = Number(match[1]);
    }
  } else if (filter && typeof filter === "object") {
    if (filter.type !== "blur") {
      throw new SceneRenderError(
        "UNSUPPORTED_FILTER",
        "The accelerated renderer supports only a blur filter.",
        { capability: true, recordId }
      );
    }
    blur = filter.radius;
  } else if (filter != null) {
    throw new SceneRenderError("INVALID_FILTER", "filter must be null, a blur string, or a blur object.", {
      recordId,
    });
  }

  const radius = Number(blur);
  if (!Number.isFinite(radius) || radius < 0 || radius > MAX_BLUR_RADIUS) {
    throw new SceneRenderError(
      "INVALID_FILTER",
      `Blur radius must be between 0 and ${MAX_BLUR_RADIUS} world pixels.`,
      { recordId }
    );
  }
  if (radius > 0 && renderer.capabilities && !renderer.capabilities.blurFilter) {
    throw new SceneRenderError(
      "BLUR_FILTER_UNAVAILABLE",
      "This OffscreenCanvas implementation does not support Canvas2D blur filters.",
      { capability: true, recordId }
    );
  }
  return radius;
}

function normalizeBlendMode(value, recordId) {
  const blendMode = String(value || "normal");
  if (!DECLARED_BLEND_MODES.includes(blendMode)) {
    throw new SceneRenderError("UNSUPPORTED_BLEND_MODE", `Blend mode \"${blendMode}\" is unsupported.`, {
      capability: true,
      recordId,
    });
  }
  if (
    renderer.capabilities &&
    !renderer.capabilities.blendModes.includes(blendMode)
  ) {
    throw new SceneRenderError(
      "BLEND_MODE_UNAVAILABLE",
      `This OffscreenCanvas implementation does not support blend mode \"${blendMode}\".`,
      { capability: true, recordId }
    );
  }
  return blendMode;
}

function normalizeRecord(raw, previous = null) {
  if (!raw || typeof raw !== "object") {
    throw new SceneRenderError("INVALID_RECORD", "Each scene record must be an object.");
  }
  const id = normalizeRecordId(raw.id);
  const sourceUrl = String(raw.sourceUrl || "").trim();
  if (!sourceUrl) {
    throw new SceneRenderError("INVALID_SOURCE", "Every stamp requires sourceUrl.", { recordId: id });
  }

  const width = Number(raw.width);
  const height = Number(raw.height);
  if (!Number.isFinite(width) || width <= 0 || !Number.isFinite(height) || height <= 0) {
    throw new SceneRenderError("INVALID_GEOMETRY", "Stamp width and height must be positive.", {
      recordId: id,
      sourceUrl,
    });
  }

  const sourceType = String(raw.sourceType || "auto").toLowerCase();
  if (!new Set(["auto", "gif", "static"]).has(sourceType)) {
    throw new SceneRenderError("INVALID_SOURCE_TYPE", 'sourceType must be "auto", "gif", or "static".', {
      recordId: id,
      sourceUrl,
    });
  }
  const animated = typeof raw.animated === "boolean" ? raw.animated : null;
  if (sourceType === "static" && animated === true) {
    throw new SceneRenderError(
      "UNSUPPORTED_ANIMATED_SOURCE",
      "A source declared animated cannot use sourceType static.",
      { capability: true, recordId: id, sourceUrl }
    );
  }

  const imageRendering = raw.imageRendering === "auto" ? "auto" : "pixelated";
  const opacity = Number(raw.opacity ?? 1);
  if (!Number.isFinite(opacity) || opacity < 0 || opacity > 1) {
    throw new SceneRenderError("INVALID_OPACITY", "Stamp opacity must be between 0 and 1.", {
      recordId: id,
    });
  }

  const tintLayersActive = hasActiveTintValue(raw.tintLayers);
  const tintSettingsActive = hasActiveTintValue(raw.tintSettings);
  if (finiteNumber(raw.tintAmount, 0) > 0 || tintLayersActive || tintSettingsActive) {
    throw new SceneRenderError(
      "UNSUPPORTED_TINT",
      "Tinted stamps require the compatibility renderer.",
      { capability: true, recordId: id, sourceUrl }
    );
  }
  if (finiteNumber(raw.pixelateAmount, 0) > 0) {
    throw new SceneRenderError(
      "UNSUPPORTED_PIXELATE_EFFECT",
      "The animated pixelate effect requires the compatibility renderer.",
      { capability: true, recordId: id, sourceUrl }
    );
  }

  const now = performance.now();
  const startedAt = raw.startedAt != null && Number.isFinite(Number(raw.startedAt))
    ? normalizeClientTimestamp(raw.startedAt, now)
    : previous?.startedAt ?? now;
  const animationPaused = raw.animationPaused === true;
  const animationPausedAt = raw.animationPausedAt != null && Number.isFinite(Number(raw.animationPausedAt))
    ? normalizeClientTimestamp(raw.animationPausedAt, now)
    : animationPaused
    ? previous?.animationPausedAt ?? now
    : null;

  return {
    id,
    key: getRecordKey(id),
    sourceUrl,
    sourceType,
    animated,
    mimeType: typeof raw.mimeType === "string" ? raw.mimeType.toLowerCase() : "",
    centerX: finiteNumber(raw.centerX, 0),
    centerY: finiteNumber(raw.centerY, 0),
    width,
    height,
    rotation: finiteNumber(raw.rotation, 0),
    opacity,
    blendMode: normalizeBlendMode(raw.blendMode, id),
    imageRendering,
    blurAmount: normalizeFilter(raw, id),
    visible: raw.visible !== false,
    startedAt,
    phaseOffsetMs: finiteNumber(raw.phaseOffsetMs, 0),
    animationPaused,
    animationPausedAt,
    insertedAt: previous?.insertedAt ?? now,
  };
}

function serializeError(error) {
  if (error instanceof SceneRenderError) {
    return {
      code: error.code,
      message: error.message,
      capability: error.capability,
      retriable: error.retriable,
      ...(error.recordId != null ? { recordId: error.recordId } : {}),
      ...(error.sourceUrl ? { sourceUrl: error.sourceUrl } : {}),
      ...(error.details ? { details: error.details } : {}),
    };
  }
  return {
    code: "RENDERER_FAILURE",
    message: error instanceof Error ? error.message : "The accelerated renderer failed.",
    capability: false,
    retriable: false,
  };
}

function postMessage(type, payload = {}) {
  workerScope?.postMessage({
    protocol: SCENE_RENDER_PROTOCOL,
    version: SCENE_RENDER_VERSION,
    type,
    ...payload,
  });
}

function postError(action, error, message = null) {
  postMessage("error", {
    action,
    ...(message?.requestId != null ? { requestId: message.requestId } : {}),
    ...(message?.revision != null ? { revision: message.revision } : {}),
    error: serializeError(error),
  });
}

function postAck(action, message, extra = {}) {
  postMessage("ack", {
    action,
    ...(message?.requestId != null ? { requestId: message.requestId } : {}),
    revision: renderer.revision,
    ...extra,
  });
}

function getCompositeOperation(blendMode) {
  return blendMode === "normal" ? "source-over" : blendMode;
}

function probeCapabilities(context) {
  const supportedBlendModes = [];
  const originalComposite = context.globalCompositeOperation;
  for (const blendMode of DECLARED_BLEND_MODES) {
    const operation = getCompositeOperation(blendMode);
    context.globalCompositeOperation = "source-over";
    context.globalCompositeOperation = operation;
    if (context.globalCompositeOperation === operation) {
      supportedBlendModes.push(blendMode);
    }
  }
  context.globalCompositeOperation = originalComposite || "source-over";

  let blurFilter = false;
  if ("filter" in context) {
    const originalFilter = context.filter;
    try {
      context.filter = "blur(1px)";
      blurFilter = context.filter === "blur(1px)";
    } catch (_error) {
      blurFilter = false;
    }
    context.filter = originalFilter || "none";
  }

  return {
    offscreenCanvas2d: true,
    moduleWorker: true,
    createImageBitmap: typeof createImageBitmap === "function",
    gif: true,
    animatedNonGif: false,
    blurFilter,
    blendModes: supportedBlendModes,
  };
}

function resizeBackingCanvas() {
  if (!renderer.canvas) {
    return;
  }
  renderer.canvas.width = Math.max(1, Math.round(renderer.width * renderer.dpr));
  renderer.canvas.height = Math.max(1, Math.round(renderer.height * renderer.dpr));
}

function getDefaultMemoryBudget() {
  const deviceMemory = finitePositive(workerScope?.navigator?.deviceMemory, 4);
  return clamp(
    Math.round(deviceMemory * 64 * 1024 * 1024),
    MIN_MEMORY_BUDGET_BYTES,
    MAX_MEMORY_BUDGET_BYTES
  );
}

function getSourceMemoryStats() {
  const canvasBytes = Math.max(1, Math.round(renderer.width * renderer.dpr)) *
    Math.max(1, Math.round(renderer.height * renderer.dpr)) * 4;
  const stats = {
    sourceCount: sourceCache.size,
    loadingSourceCount: 0,
    readySourceCount: 0,
    failedSourceCount: 0,
    gifSourceCount: 0,
    staticSourceCount: 0,
    originalFrameCount: 0,
    storedFrameCount: 0,
    bitmapPixels: 0,
    estimatedBitmapBytes: 0,
    canvasBytes,
    totalEstimatedBytes: 0,
    fetchedBytes: 0,
    memoryBudgetBytes: renderer.memoryBudgetBytes,
    reservedBitmapBytes: renderer.reservedBitmapBytes,
    stampCount: renderer.records.size,
    lodLimitedSourceCount: 0,
  };
  for (const source of sourceCache.values()) {
    if (source.status === "loading") {
      stats.loadingSourceCount += 1;
    } else if (source.status === "error") {
      stats.failedSourceCount += 1;
    } else if (source.status === "ready") {
      stats.readySourceCount += 1;
      const data = source.data;
      if (data.kind === "gif") {
        stats.gifSourceCount += 1;
      } else {
        stats.staticSourceCount += 1;
      }
      stats.originalFrameCount += data.originalFrameCount || 1;
      stats.storedFrameCount += data.frames.length;
      for (const frame of data.frames) {
        stats.bitmapPixels += frame.bitmap.width * frame.bitmap.height;
      }
      const usage = getSourceUsage(source.url);
      if (
        usage.instanceCount > 0 &&
        usage.maxProjectedCssPixels * renderer.dpr >
          Math.max(data.targetWidth, data.targetHeight) * 1.25
      ) {
        stats.lodLimitedSourceCount += 1;
      }
    }
    stats.fetchedBytes += source.byteLength || 0;
  }
  stats.estimatedBitmapBytes = stats.bitmapPixels * 4;
  stats.totalEstimatedBytes = stats.estimatedBitmapBytes + stats.canvasBytes;
  return stats;
}

function postMemoryStats(reason = "update") {
  postMessage("memory-stats", { reason, stats: getSourceMemoryStats() });
}

function postSourceStatus(source) {
  const payload = {
    sourceUrl: source.url,
    status: source.status,
    revision: renderer.revision,
  };
  if (source.status === "ready") {
    const data = source.data;
    payload.source = {
      kind: data.kind,
      width: data.width,
      height: data.height,
      animated: data.animated,
      originalFrameCount: data.originalFrameCount,
      storedFrameCount: data.frames.length,
      totalDurationMs: data.totalDurationMs,
      loopCount: data.loopCount,
      playCount: Number.isFinite(data.playCount) ? data.playCount : null,
      targetWidth: data.targetWidth,
      targetHeight: data.targetHeight,
      spatialScale: data.spatialScale,
      targetFrameIntervalMs: data.targetFrameIntervalMs,
      estimatedBitmapBytes: data.estimatedBitmapBytes,
    };
  } else if (source.status === "error") {
    payload.error = serializeError(source.error);
  }
  postMessage("source-status", payload);
}

function postSourceEvicted(sourceUrl) {
  postMessage("source-status", {
    sourceUrl,
    status: "evicted",
    revision: renderer.revision,
  });
}

function getCurrentEstimatedBitmapBytes() {
  return sumReadySourceBitmapBytes(sourceCache.values());
}

function getCanvasEstimatedBytes() {
  return Math.max(1, Math.round(renderer.width * renderer.dpr)) *
    Math.max(1, Math.round(renderer.height * renderer.dpr)) * 4;
}

function getSourceRecords(sourceUrl, recordMap = renderer.records) {
  const records = [];
  for (const record of recordMap.values()) {
    if (record.sourceUrl === sourceUrl) {
      records.push(record);
    }
  }
  return records;
}

function getSourceRequirement(sourceUrl, recordMap = renderer.records) {
  const records = getSourceRecords(sourceUrl, recordMap);
  const explicitTypes = new Set(
    records.map((record) => record.sourceType).filter((type) => type !== "auto")
  );
  if (explicitTypes.size > 1) {
    throw new SceneRenderError(
      "CONFLICTING_SOURCE_TYPES",
      "The same source URL was declared both GIF and static.",
      { capability: true, sourceUrl }
    );
  }
  const declaredAnimated = records.some((record) => record.animated === true);
  const declaredStatic = records.some((record) => record.animated === false);
  if (declaredAnimated && declaredStatic) {
    throw new SceneRenderError(
      "CONFLICTING_ANIMATION_DECLARATIONS",
      "The same source URL was declared both animated and static.",
      { capability: true, sourceUrl }
    );
  }
  return {
    sourceType: explicitTypes.values().next().value || "auto",
    declaredAnimated,
    declaredStatic,
    mimeTypes: Array.from(new Set(records.map((record) => record.mimeType).filter(Boolean))),
    records,
  };
}

function validateSourceCompatibility(sourceUrl, data, recordMap = renderer.records) {
  const requirement = getSourceRequirement(sourceUrl, recordMap);
  if (requirement.sourceType === "gif" && data.kind !== "gif") {
    throw new SceneRenderError("SOURCE_TYPE_MISMATCH", "A source declared GIF is not a GIF file.", {
      capability: true,
      sourceUrl,
    });
  }
  if (requirement.sourceType === "static" && data.kind === "gif") {
    throw new SceneRenderError("SOURCE_TYPE_MISMATCH", "A source declared static is a GIF file.", {
      capability: true,
      sourceUrl,
    });
  }
  if (requirement.declaredAnimated && data.kind !== "gif") {
    throw new SceneRenderError(
      "UNSUPPORTED_ANIMATED_SOURCE",
      "Only GIF animation is supported by the accelerated renderer.",
      { capability: true, sourceUrl }
    );
  }
  if (requirement.declaredStatic && data.animated) {
    throw new SceneRenderError(
      "SOURCE_ANIMATION_MISMATCH",
      "A source declared static contains multiple GIF frames.",
      { capability: true, sourceUrl }
    );
  }
}

function asciiAt(bytes, offset, length) {
  if (offset < 0 || offset + length > bytes.length) {
    return "";
  }
  let value = "";
  for (let index = 0; index < length; index += 1) {
    value += String.fromCharCode(bytes[offset + index]);
  }
  return value;
}

function readUint32BigEndian(bytes, offset) {
  if (offset < 0 || offset + 4 > bytes.length) {
    return 0;
  }
  return (
    bytes[offset] * 0x1000000 +
    (bytes[offset + 1] << 16) +
    (bytes[offset + 2] << 8) +
    bytes[offset + 3]
  );
}

function readUint32LittleEndian(bytes, offset) {
  if (offset < 0 || offset + 4 > bytes.length) {
    return 0;
  }
  return (
    bytes[offset] +
    (bytes[offset + 1] << 8) +
    (bytes[offset + 2] << 16) +
    bytes[offset + 3] * 0x1000000
  );
}

function inspectPngAnimation(bytes) {
  if (
    bytes.length < 8 ||
    bytes[0] !== 0x89 ||
    asciiAt(bytes, 1, 3) !== "PNG" ||
    bytes[4] !== 0x0d ||
    bytes[5] !== 0x0a
  ) {
    return false;
  }
  let offset = 8;
  while (offset + 12 <= bytes.length) {
    const length = readUint32BigEndian(bytes, offset);
    const type = asciiAt(bytes, offset + 4, 4);
    if (type === "acTL") {
      return true;
    }
    if (type === "IDAT" || type === "IEND") {
      return false;
    }
    offset += 12 + length;
  }
  return false;
}

function inspectWebpAnimation(bytes) {
  if (bytes.length < 16 || asciiAt(bytes, 0, 4) !== "RIFF" || asciiAt(bytes, 8, 4) !== "WEBP") {
    return false;
  }
  let offset = 12;
  while (offset + 8 <= bytes.length) {
    const type = asciiAt(bytes, offset, 4);
    const length = readUint32LittleEndian(bytes, offset + 4);
    if (type === "ANIM" || type === "ANMF") {
      return true;
    }
    if (type === "VP8X" && offset + 9 <= bytes.length && (bytes[offset + 8] & 0x02) !== 0) {
      return true;
    }
    offset += 8 + length + (length % 2);
  }
  return false;
}

function sniffSource(bytes, contentType = "") {
  const gifSignature = asciiAt(bytes, 0, 6);
  if (gifSignature === "GIF87a" || gifSignature === "GIF89a") {
    return { format: "gif", animatedNonGif: false };
  }
  if (inspectPngAnimation(bytes)) {
    return { format: "png", animatedNonGif: true };
  }
  if (inspectWebpAnimation(bytes)) {
    return { format: "webp", animatedNonGif: true };
  }

  const sample = new TextDecoder().decode(bytes.subarray(0, Math.min(bytes.length, 1024 * 1024)));
  const isSvg = /image\/svg\+xml/i.test(contentType) || /<svg(?:\s|>)/i.test(sample);
  if (isSvg) {
    const animated = /<(?:animate|animatecolor|animatemotion|animatetransform|set)(?:\s|>)/i.test(sample) ||
      /@keyframes\s/i.test(sample);
    return { format: "svg", animatedNonGif: animated };
  }

  const fileTypeBox = asciiAt(bytes, 4, 4) === "ftyp"
    ? asciiAt(bytes, 8, Math.min(120, Math.max(0, bytes.length - 8)))
    : "";
  if (fileTypeBox.includes("avis")) {
    return { format: "avif-sequence", animatedNonGif: true };
  }
  if (fileTypeBox.includes("avif")) {
    return { format: "avif", animatedNonGif: false };
  }
  return { format: "static", animatedNonGif: false };
}

function getGifLoopInfo(parsed) {
  const applicationFrame = Array.isArray(parsed?.frames)
    ? parsed.frames.find((frame) => {
        const id = String(frame?.application?.id || "").toUpperCase();
        return id === "NETSCAPE2.0" || id === "ANIMEXTS1.0";
      })
    : null;
  const rawBlocks = applicationFrame?.application?.blocks;
  if (!rawBlocks) {
    return { loopCount: null, playCount: 1 };
  }
  const bytes = ArrayBuffer.isView(rawBlocks)
    ? Array.from(rawBlocks)
    : Array.isArray(rawBlocks)
    ? rawBlocks
    : Object.keys(rawBlocks)
        .sort((left, right) => Number(left) - Number(right))
        .map((key) => Number(rawBlocks[key]));
  if (bytes.length < 3 || bytes[0] !== 1) {
    return { loopCount: null, playCount: 1 };
  }
  const loopCount = (bytes[1] | (bytes[2] << 8)) >>> 0;
  return {
    loopCount,
    // The Netscape field counts repetitions after the initial play. Zero is
    // the special infinite-loop value used by browsers.
    playCount: loopCount === 0 ? Infinity : loopCount + 1,
  };
}

async function readResponseBytes(response, sourceUrl) {
  const declaredLength = Number(response.headers.get("content-length"));
  if (Number.isFinite(declaredLength) && declaredLength > renderer.maxSourceBytes) {
    throw new SceneRenderError("SOURCE_TOO_LARGE", "The source exceeds the configured byte limit.", {
      sourceUrl,
      details: { byteLength: declaredLength, maxSourceBytes: renderer.maxSourceBytes },
    });
  }

  if (!response.body?.getReader) {
    const buffer = await response.arrayBuffer();
    if (buffer.byteLength > renderer.maxSourceBytes) {
      throw new SceneRenderError("SOURCE_TOO_LARGE", "The source exceeds the configured byte limit.", {
        sourceUrl,
      });
    }
    return buffer;
  }

  const reader = response.body.getReader();
  const chunks = [];
  let byteLength = 0;
  try {
    while (true) {
      if (renderer.disposed) {
        await reader.cancel("Renderer disposed.");
        throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
      }
      const { done, value } = await reader.read();
      if (done) {
        break;
      }
      byteLength += value.byteLength;
      if (byteLength > renderer.maxSourceBytes) {
        await reader.cancel("Source exceeded its byte limit.");
        throw new SceneRenderError("SOURCE_TOO_LARGE", "The source exceeds the configured byte limit.", {
          sourceUrl,
          details: { byteLength, maxSourceBytes: renderer.maxSourceBytes },
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

function invalidateSourceUsageCache() {
  renderer.sourceUsageCache = null;
}

function buildSourceUsageCache() {
  const usageByUrl = new Map();
  for (const record of renderer.records.values()) {
    let usage = usageByUrl.get(record.sourceUrl);
    if (!usage) {
      usage = {
        instanceCount: 0,
        maxWorldWidth: 1,
        maxWorldHeight: 1,
        maxProjectedCssPixels: 1,
        nearestOnly: true,
      };
      usageByUrl.set(record.sourceUrl, usage);
    }
    usage.instanceCount += 1;
    usage.maxWorldWidth = Math.max(usage.maxWorldWidth, record.width);
    usage.maxWorldHeight = Math.max(usage.maxWorldHeight, record.height);
    usage.maxProjectedCssPixels = Math.max(
      usage.maxProjectedCssPixels,
      record.width * renderer.camera.scale,
      record.height * renderer.camera.scale
    );
    usage.nearestOnly &&= record.imageRendering === "pixelated";
  }
  renderer.sourceUsageCache = usageByUrl;
  return usageByUrl;
}

function getSourceUsage(sourceUrl) {
  const usageByUrl = renderer.sourceUsageCache || buildSourceUsageCache();
  return usageByUrl.get(sourceUrl) || {
    instanceCount: 0,
    maxWorldWidth: 1,
    maxWorldHeight: 1,
    maxProjectedCssPixels: 1,
    nearestOnly: false,
  };
}

function chooseSpatialLod(sourceUrl, width, height) {
  const usage = getSourceUsage(sourceUrl);
  const nativeLongest = Math.max(width, height);
  const requestedLongest = Math.max(
    256,
    usage.maxWorldWidth * renderer.dpr,
    usage.maxWorldHeight * renderer.dpr,
    usage.maxProjectedCssPixels * renderer.dpr * 1.5
  );
  let spatialScale = 1;
  // A source can finish a queued decode after a newer scene removes its last
  // record. Cache it at native resolution in that case so a later scene does
  // not inherit a low-resolution choice made without any real usage signal.
  if (usage.instanceCount > 0 && nativeLongest > 512 && requestedLongest < nativeLongest) {
    const requiredScale = clamp(requestedLongest / nativeLongest, 0.125, 1);
    const levels = [0.125, 0.25, 0.5, 1];
    spatialScale = levels.find((level) => level >= requiredScale) || 1;
  }
  return {
    usage,
    spatialScale,
    targetWidth: Math.max(1, Math.round(width * spatialScale)),
    targetHeight: Math.max(1, Math.round(height * spatialScale)),
  };
}

function chooseFrameIntervalMs(usage, originalFrameCount, totalDurationMs, targetPixels) {
  let targetFrameIntervalMs = usage.maxProjectedCssPixels >= 192
    ? 20
    : usage.maxProjectedCssPixels >= 96
    ? 33
    : usage.maxProjectedCssPixels >= 48
    ? 50
    : usage.maxProjectedCssPixels >= 24
    ? 67
    : 100;
  if (renderer.records.size >= 8000) {
    targetFrameIntervalMs = Math.max(targetFrameIntervalMs, 50);
  } else if (renderer.records.size >= 3000) {
    targetFrameIntervalMs = Math.max(targetFrameIntervalMs, 34);
  } else if (renderer.records.size >= 1000) {
    targetFrameIntervalMs = Math.max(targetFrameIntervalMs, 25);
  }

  const availableBytes = calculateAvailableBitmapBytes(
    renderer.memoryBudgetBytes,
    getCanvasEstimatedBytes(),
    getCurrentEstimatedBitmapBytes(),
    renderer.reservedBitmapBytes
  );
  const averageDelay = Math.max(1, totalDurationMs / Math.max(1, originalFrameCount));
  let estimatedStoredFrames = Math.min(
    originalFrameCount,
    Math.max(1, Math.ceil(totalDurationMs / targetFrameIntervalMs))
  );
  let estimatedBytes = estimatedStoredFrames * targetPixels * 4;
  while (estimatedBytes > availableBytes && targetFrameIntervalMs < 1000) {
    targetFrameIntervalMs = Math.min(1000, targetFrameIntervalMs * 2);
    estimatedStoredFrames = Math.min(
      originalFrameCount,
      Math.max(1, Math.ceil(totalDurationMs / Math.max(targetFrameIntervalMs, averageDelay)))
    );
    estimatedBytes = estimatedStoredFrames * targetPixels * 4;
  }
  if (estimatedBytes > availableBytes) {
    throw new SceneRenderError(
      "SOURCE_MEMORY_BUDGET_EXCEEDED",
      "The GIF cannot be retained within the accelerated renderer memory budget.",
      { capability: true, details: { estimatedBytes, availableBytes } }
    );
  }
  return { targetFrameIntervalMs, estimatedBytes };
}

function getGifFrameDelayMs(frame) {
  if (!frame?.gce) {
    return DEFAULT_GIF_FRAME_DELAY_MS;
  }
  const centiseconds = Number(frame.gce.delay);
  return Math.max(
    20,
    Number.isFinite(centiseconds) && centiseconds > 0
      ? Math.round(centiseconds * 10)
      : 100
  );
}

async function createSnapshotBitmap(
  canvas,
  targetWidth,
  targetHeight,
  scratchCanvas,
  scratchContext,
  imageSmoothing
) {
  scratchContext.setTransform(1, 0, 0, 1, 0, 0);
  scratchContext.globalAlpha = 1;
  scratchContext.globalCompositeOperation = "copy";
  scratchContext.imageSmoothingEnabled = imageSmoothing;
  if (imageSmoothing && "imageSmoothingQuality" in scratchContext) {
    scratchContext.imageSmoothingQuality = "high";
  }
  scratchContext.clearRect(0, 0, targetWidth, targetHeight);
  scratchContext.drawImage(canvas, 0, 0, canvas.width, canvas.height, 0, 0, targetWidth, targetHeight);
  scratchContext.globalCompositeOperation = "source-over";
  return createImageBitmap(scratchCanvas);
}

async function decodeGifSource(sourceUrl, arrayBuffer) {
  let parsed;
  try {
    parsed = parseGIF(arrayBuffer);
  } catch (error) {
    throw new SceneRenderError("GIF_PARSE_FAILED", "The GIF could not be parsed.", {
      sourceUrl,
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }

  const width = Math.trunc(Number(parsed?.lsd?.width) || 0);
  const height = Math.trunc(Number(parsed?.lsd?.height) || 0);
  const logicalPixels = width * height;
  if (width <= 0 || height <= 0 || !Number.isSafeInteger(logicalPixels)) {
    throw new SceneRenderError("INVALID_GIF_DIMENSIONS", "The GIF has invalid logical dimensions.", {
      sourceUrl,
    });
  }
  const adaptiveLogicalPixelLimit = Math.min(
    MAX_GIF_LOGICAL_PIXELS,
    Math.max(1, Math.floor(renderer.memoryBudgetBytes / 16))
  );
  if (logicalPixels > adaptiveLogicalPixelLimit) {
    throw new SceneRenderError(
      "GIF_CANVAS_TOO_LARGE",
      "The GIF logical canvas exceeds the accelerated renderer safety limit.",
      {
        capability: true,
        sourceUrl,
        details: { width, height, logicalPixels, maxLogicalPixels: adaptiveLogicalPixelLimit },
      }
    );
  }

  const imageFrames = Array.isArray(parsed?.frames)
    ? parsed.frames.filter((frame) => frame?.image)
    : [];
  if (!imageFrames.length) {
    throw new SceneRenderError("GIF_HAS_NO_FRAMES", "The GIF contains no image frames.", { sourceUrl });
  }
  if (imageFrames.length > MAX_GIF_FRAMES) {
    throw new SceneRenderError("GIF_HAS_TOO_MANY_FRAMES", "The GIF exceeds the frame safety limit.", {
      capability: true,
      sourceUrl,
      details: { frameCount: imageFrames.length, maxFrameCount: MAX_GIF_FRAMES },
    });
  }

  const frameDelays = imageFrames.map(getGifFrameDelayMs);
  const totalDurationMs = frameDelays.reduce((total, delay) => total + delay, 0);
  const loopInfo = getGifLoopInfo(parsed);
  const lod = chooseSpatialLod(sourceUrl, width, height);
  const frameLod = chooseFrameIntervalMs(
    lod.usage,
    imageFrames.length,
    totalDurationMs,
    lod.targetWidth * lod.targetHeight
  );
  renderer.reservedBitmapBytes += frameLod.estimatedBytes;

  if (typeof OffscreenCanvas !== "function") {
    renderer.reservedBitmapBytes -= frameLod.estimatedBytes;
    throw new SceneRenderError(
      "OFFSCREEN_CANVAS_UNAVAILABLE",
      "Worker-owned OffscreenCanvas decode surfaces are unavailable.",
      { capability: true, sourceUrl }
    );
  }

  const compositeCanvas = new OffscreenCanvas(width, height);
  const compositeContext = compositeCanvas.getContext("2d", { alpha: true });
  const patchCanvas = new OffscreenCanvas(1, 1);
  let patchContext = patchCanvas.getContext("2d", { alpha: true });
  const restoreCanvas = new OffscreenCanvas(width, height);
  const restoreContext = restoreCanvas.getContext("2d", { alpha: true });
  const snapshotCanvas = new OffscreenCanvas(lod.targetWidth, lod.targetHeight);
  const snapshotContext = snapshotCanvas.getContext("2d", { alpha: true });
  if (!compositeContext || !patchContext || !restoreContext || !snapshotContext) {
    renderer.reservedBitmapBytes -= frameLod.estimatedBytes;
    throw new SceneRenderError("OFFSCREEN_2D_UNAVAILABLE", "Could not create GIF decode canvases.", {
      capability: true,
      sourceUrl,
    });
  }

  compositeContext.clearRect(0, 0, width, height);
  const frames = [];
  let elapsedSinceStoredFrame = Infinity;

  try {
    for (let index = 0; index < imageFrames.length; index += 1) {
      if (renderer.disposed) {
        throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
      }
      const frame = imageFrames[index];
      const descriptor = frame.image.descriptor;
      const frameWidth = Math.max(1, Math.trunc(Number(descriptor.width) || width));
      const frameHeight = Math.max(1, Math.trunc(Number(descriptor.height) || height));
      const left = Math.trunc(Number(descriptor.left) || 0);
      const top = Math.trunc(Number(descriptor.top) || 0);
      const disposalType = Number(frame?.gce?.extras?.disposal) || 0;

      if (disposalType === 3) {
        restoreContext.setTransform(1, 0, 0, 1, 0, 0);
        restoreContext.globalCompositeOperation = "copy";
        restoreContext.clearRect(0, 0, width, height);
        restoreContext.drawImage(compositeCanvas, 0, 0);
        restoreContext.globalCompositeOperation = "source-over";
      }

      let decoded;
      try {
        decoded = decompressFrame(frame, parsed.gct, true);
      } catch (error) {
        throw new SceneRenderError("GIF_FRAME_DECODE_FAILED", "A GIF frame could not be decoded.", {
          sourceUrl,
          details: { frameIndex: index, cause: error instanceof Error ? error.message : "unknown error" },
        });
      }
      if (!decoded?.patch || decoded.patch.length !== frameWidth * frameHeight * 4) {
        throw new SceneRenderError("GIF_FRAME_DECODE_FAILED", "A GIF frame decoded incompletely.", {
          sourceUrl,
          details: { frameIndex: index },
        });
      }

      if (patchCanvas.width !== frameWidth || patchCanvas.height !== frameHeight) {
        patchCanvas.width = frameWidth;
        patchCanvas.height = frameHeight;
        patchContext = patchCanvas.getContext("2d", { alpha: true });
      }
      if (!patchContext) {
        throw new SceneRenderError("OFFSCREEN_2D_UNAVAILABLE", "Could not create a GIF patch context.", {
          capability: true,
          sourceUrl,
        });
      }
      const patchImage = patchContext.createImageData(frameWidth, frameHeight);
      patchImage.data.set(decoded.patch);
      patchContext.clearRect(0, 0, frameWidth, frameHeight);
      patchContext.putImageData(patchImage, 0, 0);
      compositeContext.drawImage(patchCanvas, left, top);

      const frameDelay = frameDelays[index];
      const shouldStore =
        index === 0 ||
        index === imageFrames.length - 1 ||
        elapsedSinceStoredFrame >= frameLod.targetFrameIntervalMs;
      if (shouldStore) {
        const bitmap = await createSnapshotBitmap(
          compositeCanvas,
          lod.targetWidth,
          lod.targetHeight,
          snapshotCanvas,
          snapshotContext,
          !lod.usage.nearestOnly
        );
        frames.push({ bitmap, durationMs: frameDelay, cumulativeEndMs: 0 });
        elapsedSinceStoredFrame = frameDelay;
      } else {
        frames[frames.length - 1].durationMs += frameDelay;
        elapsedSinceStoredFrame += frameDelay;
      }

      // Disposal is processed for every source frame, including frames omitted
      // from the stored temporal LOD. This preserves all later composites.
      if (disposalType === 2) {
        compositeContext.clearRect(left, top, frameWidth, frameHeight);
      } else if (disposalType === 3) {
        compositeContext.save();
        compositeContext.globalCompositeOperation = "copy";
        compositeContext.drawImage(restoreCanvas, 0, 0);
        compositeContext.restore();
      }

      if ((index + 1) % SOURCE_PROGRESS_INTERVAL === 0) {
        postMessage("source-progress", {
          sourceUrl,
          decodedFrames: index + 1,
          totalFrames: imageFrames.length,
        });
        await new Promise((resolve) => setTimeout(resolve, 0));
      }
    }
  } catch (error) {
    for (const frame of frames) {
      frame.bitmap.close?.();
    }
    throw error;
  } finally {
    renderer.reservedBitmapBytes = Math.max(
      0,
      renderer.reservedBitmapBytes - frameLod.estimatedBytes
    );
  }

  let cumulativeEndMs = 0;
  for (const frame of frames) {
    cumulativeEndMs += frame.durationMs;
    frame.cumulativeEndMs = cumulativeEndMs;
  }
  const estimatedBitmapBytes = frames.reduce(
    (total, frame) => total + frame.bitmap.width * frame.bitmap.height * 4,
    0
  );
  const otherReservedBytes = renderer.reservedBitmapBytes;
  const availableBytes = calculateAvailableBitmapBytes(
    renderer.memoryBudgetBytes,
    getCanvasEstimatedBytes(),
    getCurrentEstimatedBitmapBytes(),
    otherReservedBytes
  );
  if (estimatedBitmapBytes > availableBytes) {
    for (const frame of frames) {
      frame.bitmap.close?.();
    }
    throw new SceneRenderError(
      "SOURCE_MEMORY_BUDGET_EXCEEDED",
      "The decoded GIF exceeded the accelerated renderer memory budget.",
      {
        capability: true,
        sourceUrl,
        details: { estimatedBitmapBytes, availableBytes },
      }
    );
  }
  if (renderer.disposed) {
    for (const frame of frames) {
      frame.bitmap.close?.();
    }
    throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
  }
  return {
    kind: "gif",
    width,
    height,
    animated: imageFrames.length > 1,
    originalFrameCount: imageFrames.length,
    frames,
    totalDurationMs: cumulativeEndMs || DEFAULT_GIF_FRAME_DELAY_MS,
    loopCount: loopInfo.loopCount,
    playCount: loopInfo.playCount,
    targetWidth: lod.targetWidth,
    targetHeight: lod.targetHeight,
    spatialScale: lod.spatialScale,
    targetFrameIntervalMs: frameLod.targetFrameIntervalMs,
    estimatedBitmapBytes,
  };
}

async function decodeStaticSource(sourceUrl, arrayBuffer, contentType) {
  const blob = new Blob([arrayBuffer], { type: contentType || "application/octet-stream" });
  let bitmap;
  try {
    bitmap = await createImageBitmap(blob);
  } catch (error) {
    throw new SceneRenderError("STATIC_IMAGE_DECODE_FAILED", "The static image could not be decoded.", {
      sourceUrl,
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }
  if (bitmap.width <= 0 || bitmap.height <= 0) {
    bitmap.close?.();
    throw new SceneRenderError("STATIC_IMAGE_DECODE_FAILED", "The static image has invalid dimensions.", {
      sourceUrl,
    });
  }
  if (renderer.disposed) {
    bitmap.close?.();
    throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
  }

  const nativeWidth = bitmap.width;
  const nativeHeight = bitmap.height;
  const nativePixels = nativeWidth * nativeHeight;
  if (
    !Number.isSafeInteger(nativePixels) ||
    nativePixels > Math.min(MAX_GIF_LOGICAL_PIXELS, Math.floor(renderer.memoryBudgetBytes / 4))
  ) {
    bitmap.close?.();
    throw new SceneRenderError(
      "STATIC_IMAGE_TOO_LARGE",
      "The static image dimensions exceed the renderer memory safety limit.",
      { capability: true, sourceUrl, details: { nativeWidth, nativeHeight, nativePixels } }
    );
  }
  const nativeBitmapBytes = nativePixels * 4;
  const lod = chooseSpatialLod(sourceUrl, bitmap.width, bitmap.height);
  const initialAvailableBytes = calculateAvailableBitmapBytes(
    renderer.memoryBudgetBytes,
    getCanvasEstimatedBytes(),
    getCurrentEstimatedBitmapBytes(),
    renderer.reservedBitmapBytes
  );
  if (nativeBitmapBytes > initialAvailableBytes) {
    bitmap.close?.();
    throw new SceneRenderError(
      "SOURCE_MEMORY_BUDGET_EXCEEDED",
      "The decoded static image cannot coexist within the renderer memory budget.",
      {
        capability: true,
        sourceUrl,
        details: {
          estimatedBitmapBytes: nativeBitmapBytes,
          availableBytes: initialAvailableBytes,
        },
      }
    );
  }
  // createImageBitmap has already produced the native bitmap. Reserve it while
  // deciding whether a smaller LOD bitmap can be created alongside it; the
  // existing cached source remains included by getCurrentEstimatedBitmapBytes.
  let reservedBytes = nativeBitmapBytes;
  renderer.reservedBitmapBytes += nativeBitmapBytes;
  try {
    if (lod.spatialScale < 1) {
      const resizedBitmapBytes = lod.targetWidth * lod.targetHeight * 4;
      const resizeAvailableBytes = calculateAvailableBitmapBytes(
        renderer.memoryBudgetBytes,
        getCanvasEstimatedBytes(),
        getCurrentEstimatedBitmapBytes(),
        renderer.reservedBitmapBytes
      );
      if (resizedBitmapBytes <= resizeAvailableBytes) {
        reservedBytes += resizedBitmapBytes;
        renderer.reservedBitmapBytes += resizedBitmapBytes;
        try {
          const resized = await createImageBitmap(bitmap, 0, 0, bitmap.width, bitmap.height, {
            resizeWidth: lod.targetWidth,
            resizeHeight: lod.targetHeight,
            resizeQuality: lod.usage.nearestOnly ? "pixelated" : "high",
          });
          bitmap.close?.();
          bitmap = resized;
        } catch (_error) {
          // Keeping the full-resolution bitmap is conservative and visually
          // exact when resize options are unavailable.
          lod.targetWidth = bitmap.width;
          lod.targetHeight = bitmap.height;
          lod.spatialScale = 1;
        }
      } else {
        // A resize requires native and target bitmaps to coexist. Keep the
        // native bitmap when only that steady-state allocation fits.
        lod.targetWidth = bitmap.width;
        lod.targetHeight = bitmap.height;
        lod.spatialScale = 1;
      }
    }

    const estimatedBitmapBytes = bitmap.width * bitmap.height * 4;
    const otherReservedBytes = Math.max(0, renderer.reservedBitmapBytes - reservedBytes);
    const availableBytes = calculateAvailableBitmapBytes(
      renderer.memoryBudgetBytes,
      getCanvasEstimatedBytes(),
      getCurrentEstimatedBitmapBytes(),
      otherReservedBytes
    );
    if (estimatedBitmapBytes > availableBytes || renderer.disposed) {
      bitmap.close?.();
      if (renderer.disposed) {
        throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
      }
      throw new SceneRenderError(
        "SOURCE_MEMORY_BUDGET_EXCEEDED",
        "The static image cannot be retained within the renderer memory budget.",
        { capability: true, sourceUrl, details: { estimatedBitmapBytes, availableBytes } }
      );
    }
    return {
      kind: "static",
      width: nativeWidth,
      height: nativeHeight,
      animated: false,
      originalFrameCount: 1,
      frames: [{ bitmap, durationMs: Infinity, cumulativeEndMs: Infinity }],
      totalDurationMs: 0,
      targetWidth: bitmap.width,
      targetHeight: bitmap.height,
      spatialScale: lod.spatialScale,
      targetFrameIntervalMs: 0,
      estimatedBitmapBytes,
    };
  } finally {
    renderer.reservedBitmapBytes = Math.max(0, renderer.reservedBitmapBytes - reservedBytes);
  }
}

async function fetchAndDecodeSource(sourceUrl) {
  if (renderer.disposed) {
    throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
  }
  const requirement = getSourceRequirement(sourceUrl);
  let response;
  try {
    response = await fetch(sourceUrl, { credentials: "same-origin" });
  } catch (error) {
    throw new SceneRenderError("SOURCE_FETCH_FAILED", "The image source could not be fetched.", {
      retriable: true,
      sourceUrl,
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }
  if (!response.ok) {
    throw new SceneRenderError(
      "SOURCE_FETCH_FAILED",
      `The image request failed with HTTP ${response.status}.`,
      { retriable: response.status >= 500, sourceUrl, details: { status: response.status } }
    );
  }

  const contentType = String(response.headers.get("content-type") || "").split(";")[0].trim();
  const arrayBuffer = await readResponseBytes(response, sourceUrl);
  const bytes = new Uint8Array(arrayBuffer);
  const inspection = sniffSource(bytes, contentType);

  if (inspection.animatedNonGif || (requirement.declaredAnimated && inspection.format !== "gif")) {
    throw new SceneRenderError(
      "UNSUPPORTED_ANIMATED_SOURCE",
      `Animated ${inspection.format.toUpperCase()} is not supported by the accelerated renderer.`,
      { capability: true, sourceUrl, details: { format: inspection.format } }
    );
  }
  if (
    inspection.format === "svg" &&
    requirement.sourceType !== "static" &&
    !requirement.records.every((record) => record.animated === false)
  ) {
    throw new SceneRenderError(
      "AMBIGUOUS_ANIMATION_SUPPORT",
      "SVG sources must be explicitly declared static before accelerated rendering.",
      { capability: true, sourceUrl, details: { format: inspection.format } }
    );
  }
  if (requirement.sourceType === "gif" && inspection.format !== "gif") {
    throw new SceneRenderError("SOURCE_TYPE_MISMATCH", "A source declared GIF is not a GIF file.", {
      capability: true,
      sourceUrl,
      details: { detectedFormat: inspection.format },
    });
  }
  if (requirement.sourceType === "static" && inspection.format === "gif") {
    throw new SceneRenderError("SOURCE_TYPE_MISMATCH", "A source declared static is a GIF file.", {
      capability: true,
      sourceUrl,
    });
  }

  const data = inspection.format === "gif"
    ? await decodeGifSource(sourceUrl, arrayBuffer)
    : await decodeStaticSource(sourceUrl, arrayBuffer, contentType);
  validateSourceCompatibility(sourceUrl, data);
  return { data, byteLength: arrayBuffer.byteLength };
}

function ensureSourceReady(sourceUrl) {
  let source = sourceCache.get(sourceUrl);
  if (source?.status === "ready") {
    try {
      validateSourceCompatibility(sourceUrl, source.data);
      return Promise.resolve(source.data);
    } catch (error) {
      return Promise.reject(error);
    }
  }
  if (source?.status === "error") {
    return Promise.reject(source.error);
  }
  if (source?.status === "loading") {
    return source.promise.then((data) => {
      validateSourceCompatibility(sourceUrl, data);
      return data;
    });
  }

  source = {
    url: sourceUrl,
    status: "loading",
    promise: null,
    data: null,
    error: null,
    byteLength: 0,
    evictWhenReady: false,
    reloadPromise: null,
    lastLodAttemptKey: "",
  };
  sourceCache.set(sourceUrl, source);
  postSourceStatus(source);

  source.promise = renderer.sourceQueue
    .add(() => fetchAndDecodeSource(sourceUrl))
    .then(({ data, byteLength }) => {
      if (renderer.disposed) {
        closeSourceData(data);
        throw new SceneRenderError("RENDERER_DISPOSED", "The renderer was disposed.");
      }
      source.status = "ready";
      source.data = data;
      source.byteLength = byteLength;
      postSourceStatus(source);
      postMemoryStats("source-ready");
      scheduleRender(0);
      if (source.evictWhenReady || getSourceUsage(sourceUrl).instanceCount === 0) {
        closeSourceData(data);
        if (sourceCache.get(sourceUrl) === source) {
          sourceCache.delete(sourceUrl);
          postSourceEvicted(sourceUrl);
        }
      } else {
        scheduleSourceMaintenance();
        presentCurrentScene("source-ready");
      }
      return data;
    })
    .catch((error) => {
      source.status = "error";
      source.error = error instanceof SceneRenderError
        ? error
        : new SceneRenderError("SOURCE_DECODE_FAILED", "The source could not be decoded.", {
            sourceUrl,
            details: { cause: error instanceof Error ? error.message : "unknown error" },
          });
      postSourceStatus(source);
      postMemoryStats("source-error");
      scheduleRender(0);
      if (source.evictWhenReady || getSourceUsage(sourceUrl).instanceCount === 0) {
        sourceCache.delete(sourceUrl);
      }
      throw source.error;
    });
  return source.promise;
}

function getRecordBounds(record) {
  const radians = (record.rotation * Math.PI) / 180;
  const absCos = Math.abs(Math.cos(radians));
  const absSin = Math.abs(Math.sin(radians));
  const halfWidth = record.width / 2;
  const halfHeight = record.height / 2;
  const extentX = halfWidth * absCos + halfHeight * absSin + record.blurAmount * 3;
  const extentY = halfWidth * absSin + halfHeight * absCos + record.blurAmount * 3;
  return {
    left: record.centerX - extentX,
    top: record.centerY - extentY,
    right: record.centerX + extentX,
    bottom: record.centerY + extentY,
  };
}

function intersectsViewport(record) {
  const scale = renderer.camera.scale;
  const viewport = {
    left: -renderer.camera.x / scale,
    top: -renderer.camera.y / scale,
    right: (renderer.width - renderer.camera.x) / scale,
    bottom: (renderer.height - renderer.camera.y) / scale,
  };
  const bounds = getRecordBounds(record);
  return !(
    bounds.right <= viewport.left ||
    bounds.left >= viewport.right ||
    bounds.bottom <= viewport.top ||
    bounds.top >= viewport.bottom
  );
}

function resolveFrame(data, record, now) {
  if (!data.animated || data.frames.length <= 1 || data.totalDurationMs <= 0) {
    return { frame: data.frames[0], nextDelayMs: Infinity };
  }
  const clockNow = record.animationPaused
    ? record.animationPausedAt ?? record.startedAt
    : now;
  let wrapped = clockNow - record.startedAt + record.phaseOffsetMs;
  const playCount = Number(data.playCount);
  if (
    Number.isFinite(playCount) &&
    playCount > 0 &&
    wrapped >= data.totalDurationMs * playCount
  ) {
    return { frame: data.frames[data.frames.length - 1], nextDelayMs: Infinity };
  }
  wrapped %= data.totalDurationMs;
  if (wrapped < 0) {
    wrapped += data.totalDurationMs;
  }

  let low = 0;
  let high = data.frames.length - 1;
  while (low < high) {
    const middle = (low + high) >> 1;
    if (wrapped < data.frames[middle].cumulativeEndMs) {
      high = middle;
    } else {
      low = middle + 1;
    }
  }
  const frame = data.frames[low];
  return {
    frame,
    nextDelayMs: record.animationPaused
      ? Infinity
      : Math.max(1, frame.cumulativeEndMs - wrapped),
  };
}

function getAdaptiveMinimumFrameInterval() {
  const visibleCount = renderer.records.size;
  if (visibleCount >= 8000) {
    return 50;
  }
  if (visibleCount >= 3000) {
    return 1000 / 30;
  }
  if (visibleCount >= 1000) {
    return 25;
  }
  return 1000 / 60;
}

function drawScene(now = performance.now()) {
  if (!renderer.initialized || renderer.disposed || !renderer.context) {
    return Infinity;
  }
  const context = renderer.context;
  context.setTransform(renderer.dpr, 0, 0, renderer.dpr, 0, 0);
  context.globalAlpha = 1;
  context.globalCompositeOperation = "source-over";
  if ("filter" in context) {
    context.filter = "none";
  }
  context.clearRect(0, 0, renderer.width, renderer.height);
  context.translate(renderer.camera.x, renderer.camera.y);
  context.scale(renderer.camera.scale, renderer.camera.scale);

  let nextDelayMs = Infinity;
  for (const key of renderer.order) {
    const record = renderer.records.get(key);
    if (!record || !record.visible || record.opacity <= 0 || !intersectsViewport(record)) {
      continue;
    }
    const source = sourceCache.get(record.sourceUrl);
    if (!source || source.status !== "ready") {
      continue;
    }
    const resolved = resolveFrame(source.data, record, now);
    if (!resolved.frame?.bitmap) {
      continue;
    }
    nextDelayMs = Math.min(nextDelayMs, resolved.nextDelayMs);

    context.save();
    context.globalAlpha = record.opacity;
    context.globalCompositeOperation = getCompositeOperation(record.blendMode);
    context.imageSmoothingEnabled = record.imageRendering === "auto";
    if ("imageSmoothingQuality" in context && record.imageRendering === "auto") {
      context.imageSmoothingQuality = "high";
    }
    if (record.blurAmount > 0 && "filter" in context) {
      context.filter = `blur(${(record.blurAmount * renderer.camera.scale).toFixed(3)}px)`;
    }
    context.translate(record.centerX, record.centerY);
    context.rotate((record.rotation * Math.PI) / 180);
    context.drawImage(
      resolved.frame.bitmap,
      -record.width / 2,
      -record.height / 2,
      record.width,
      record.height
    );
    context.restore();
  }

  renderer.lastDrawAt = now;
  if (renderer.paused || !Number.isFinite(nextDelayMs)) {
    return Infinity;
  }
  return Math.max(getAdaptiveMinimumFrameInterval(), nextDelayMs);
}

function cancelScheduledRender() {
  if (renderer.renderTimerId !== null) {
    clearTimeout(renderer.renderTimerId);
    renderer.renderTimerId = null;
  }
  renderer.renderDueAt = Infinity;
}

function scheduleRender(delayMs = 0) {
  if (!renderer.initialized || renderer.disposed) {
    return;
  }
  const delay = Math.max(0, finiteNumber(delayMs, 0));
  const dueAt = performance.now() + delay;
  if (renderer.renderTimerId !== null && dueAt >= renderer.renderDueAt - 1) {
    return;
  }
  cancelScheduledRender();
  renderer.renderDueAt = dueAt;
  renderer.renderTimerId = setTimeout(() => {
    renderer.renderTimerId = null;
    renderer.renderDueAt = Infinity;
    const nextDelay = drawScene(renderer.paused ? renderer.pausedAt : performance.now());
    if (Number.isFinite(nextDelay)) {
      scheduleRender(nextDelay);
    }
  }, delay);
}

function areAllCurrentSceneSourcesReady() {
  for (const record of renderer.records.values()) {
    if (sourceCache.get(record.sourceUrl)?.status !== "ready") {
      return false;
    }
  }
  return true;
}

function presentCurrentScene(reason = "source-ready") {
  if (
    !renderer.initialized ||
    renderer.disposed ||
    !areAllCurrentSceneSourcesReady()
  ) {
    return false;
  }
  cancelScheduledRender();
  const nextDelay = drawScene(renderer.paused ? renderer.pausedAt : performance.now());
  if (Number.isFinite(nextDelay)) {
    scheduleRender(nextDelay);
  }
  postMessage("frame-presented", {
    action: "scene",
    revision: renderer.revision,
    reason,
  });
  return true;
}

function closeSourceData(data) {
  if (!data?.frames) {
    return;
  }
  for (const frame of data.frames) {
    frame.bitmap?.close?.();
  }
}

function pruneUnusedSources() {
  for (const [sourceUrl, source] of sourceCache) {
    if (getSourceUsage(sourceUrl).instanceCount > 0) {
      source.evictWhenReady = false;
      continue;
    }
    if (source.status === "loading" || source.reloadPromise) {
      source.evictWhenReady = true;
      continue;
    }
    if (source.status === "ready") {
      closeSourceData(source.data);
    }
    sourceCache.delete(sourceUrl);
    postSourceEvicted(sourceUrl);
  }
}

function getDesiredSourceLod(sourceUrl, source) {
  if (source?.status !== "ready") {
    return null;
  }
  const usage = getSourceUsage(sourceUrl);
  if (usage.instanceCount <= 0) {
    return null;
  }
  const nativeLongest = Math.max(source.data.width, source.data.height);
  const targetLongest = Math.max(source.data.targetWidth, source.data.targetHeight);
  const requestedLongest = Math.min(
    nativeLongest,
    Math.max(
      256,
      usage.maxWorldWidth * renderer.dpr,
      usage.maxWorldHeight * renderer.dpr,
      usage.maxProjectedCssPixels * renderer.dpr * 1.5
    )
  );
  let desiredFrameIntervalMs = usage.maxProjectedCssPixels >= 192
    ? 20
    : usage.maxProjectedCssPixels >= 96
    ? 33
    : usage.maxProjectedCssPixels >= 48
    ? 50
    : usage.maxProjectedCssPixels >= 24
    ? 67
    : 100;
  if (renderer.records.size >= 8000) {
    desiredFrameIntervalMs = Math.max(desiredFrameIntervalMs, 50);
  } else if (renderer.records.size >= 3000) {
    desiredFrameIntervalMs = Math.max(desiredFrameIntervalMs, 34);
  } else if (renderer.records.size >= 1000) {
    desiredFrameIntervalMs = Math.max(desiredFrameIntervalMs, 25);
  }
  const needsSpatialUpgrade =
    targetLongest < nativeLongest && requestedLongest > targetLongest * 1.25;
  const needsTemporalUpgrade =
    source.data.kind === "gif" &&
    source.data.targetFrameIntervalMs > desiredFrameIntervalMs * 1.25;
  if (!needsSpatialUpgrade && !needsTemporalUpgrade) {
    return null;
  }
  return {
    key: `${Math.ceil(requestedLongest)}:${Math.ceil(desiredFrameIntervalMs)}:${renderer.records.size}`,
    needsSpatialUpgrade,
    needsTemporalUpgrade,
  };
}

async function upgradeSourceLod(sourceUrl, source, requirement) {
  if (
    renderer.disposed ||
    sourceCache.get(sourceUrl) !== source ||
    source.reloadPromise ||
    source.lastLodAttemptKey === requirement.key
  ) {
    return;
  }
  source.lastLodAttemptKey = requirement.key;
  source.reloadPromise = renderer.sourceQueue.add(async () => {
    try {
      const { data, byteLength } = await fetchAndDecodeSource(sourceUrl);
      if (
        renderer.disposed ||
        sourceCache.get(sourceUrl) !== source ||
        getSourceUsage(sourceUrl).instanceCount <= 0
      ) {
        closeSourceData(data);
        return;
      }
      const oldData = source.data;
      const oldLongest = Math.max(oldData.targetWidth, oldData.targetHeight);
      const nextLongest = Math.max(data.targetWidth, data.targetHeight);
      const spatiallyImproved = nextLongest > oldLongest;
      const temporallyImproved =
        data.kind === "gif" &&
        oldData.kind === "gif" &&
        data.targetFrameIntervalMs < oldData.targetFrameIntervalMs;
      if (!spatiallyImproved && !temporallyImproved) {
        closeSourceData(data);
        return;
      }
      source.data = data;
      source.byteLength = byteLength;
      closeSourceData(oldData);
      postSourceStatus(source);
      postMemoryStats("source-lod-upgraded");
      scheduleRender(0);
    } catch (_error) {
      // Retain the existing exact-timing/low-resolution source. A stronger
      // future usage requirement gets a new attempt key and may retry.
    }
  });
  try {
    await source.reloadPromise;
  } finally {
    source.reloadPromise = null;
    if (source.evictWhenReady) {
      pruneUnusedSources();
    }
    scheduleSourceMaintenance(180);
  }
}

function scheduleSourceMaintenance(delayMs = 120) {
  if (renderer.disposed || renderer.sourceMaintenanceTimerId !== null) {
    return;
  }
  renderer.sourceMaintenanceTimerId = setTimeout(() => {
    renderer.sourceMaintenanceTimerId = null;
    pruneUnusedSources();
    for (const [sourceUrl, source] of sourceCache) {
      const requirement = getDesiredSourceLod(sourceUrl, source);
      if (
        requirement &&
        !source.reloadPromise &&
        source.lastLodAttemptKey !== requirement.key
      ) {
        void upgradeSourceLod(sourceUrl, source, requirement);
        break;
      }
    }
  }, Math.max(0, finiteNumber(delayMs, 120)));
}

function getDeltaRevision(message) {
  const revision = normalizeRevision(message.revision);
  if (revision < renderer.revision) {
    postAck(message.type, message, { ignored: true, reason: "stale-revision" });
    return null;
  }
  return revision;
}

async function handleScene(message) {
  const revision = normalizeRevision(message.revision);
  if (revision < renderer.revision) {
    postAck("scene", message, { ignored: true, reason: "stale-revision" });
    return;
  }
  if (!Array.isArray(message.records)) {
    throw new SceneRenderError("INVALID_SCENE", "scene.records must be an ordered array.");
  }

  const records = new Map();
  const order = [];
  for (const raw of message.records) {
    const record = normalizeRecord(raw);
    if (records.has(record.key)) {
      throw new SceneRenderError("DUPLICATE_RECORD_ID", "Scene record ids must be unique.", {
        recordId: record.id,
      });
    }
    records.set(record.key, record);
    order.push(record.key);
  }

  renderer.records = records;
  renderer.order = order;
  invalidateSourceUsageCache();
  renderer.revision = revision;
  renderer.sceneGeneration += 1;
  pruneUnusedSources();
  const generation = renderer.sceneGeneration;
  scheduleRender(0);

  const sourceUrls = Array.from(new Set(order.map((key) => records.get(key).sourceUrl)));
  const settled = await Promise.allSettled(sourceUrls.map((url) => ensureSourceReady(url)));
  if (
    renderer.disposed ||
    generation !== renderer.sceneGeneration ||
    revision !== renderer.revision
  ) {
    return;
  }

  const errors = [];
  settled.forEach((result, index) => {
    if (result.status === "rejected") {
      errors.push({ sourceUrl: sourceUrls[index], error: serializeError(result.reason) });
    }
  });
  if (errors.length) {
    postMessage("scene-error", {
      revision,
      ...(message.requestId != null ? { requestId: message.requestId } : {}),
      errors,
    });
    return;
  }

  cancelScheduledRender();
  const nextDelay = drawScene(renderer.paused ? renderer.pausedAt : performance.now());
  if (Number.isFinite(nextDelay)) {
    scheduleRender(nextDelay);
  }
  postMessage("scene-ready", {
    revision,
    ...(message.requestId != null ? { requestId: message.requestId } : {}),
    sourceCount: sourceUrls.length,
    stampCount: records.size,
    stats: getSourceMemoryStats(),
  });
}

function handleUpsert(message) {
  const revision = getDeltaRevision(message);
  if (revision === null) {
    return;
  }
  const rawRecords = Array.isArray(message.records)
    ? message.records
    : message.record
    ? [message.record]
    : [];
  if (!rawRecords.length) {
    throw new SceneRenderError("INVALID_UPSERT", "upsert requires record or records.");
  }

  const normalized = rawRecords.map((raw) => {
    const id = normalizeRecordId(raw?.id);
    return normalizeRecord(raw, renderer.records.get(getRecordKey(id)) || null);
  });
  if (new Set(normalized.map((record) => record.key)).size !== normalized.length) {
    throw new SceneRenderError("DUPLICATE_RECORD_ID", "An upsert batch cannot repeat a record id.");
  }
  const candidateRecords = new Map(renderer.records);
  for (const record of normalized) {
    candidateRecords.set(record.key, record);
  }
  for (const sourceUrl of new Set(normalized.map((record) => record.sourceUrl))) {
    getSourceRequirement(sourceUrl, candidateRecords);
    const source = sourceCache.get(sourceUrl);
    if (source?.status === "ready") {
      validateSourceCompatibility(sourceUrl, source.data, candidateRecords);
    }
  }

  for (const record of normalized) {
    if (!renderer.records.has(record.key)) {
      renderer.order.push(record.key);
    }
    renderer.records.set(record.key, record);
  }
  invalidateSourceUsageCache();
  renderer.revision = revision;
  renderer.sceneGeneration += 1;
  scheduleSourceMaintenance();
  const sourceUrls = Array.from(new Set(normalized.map((record) => record.sourceUrl)));
  const sceneSourcesReady = areAllCurrentSceneSourcesReady();
  if (sceneSourcesReady) {
    cancelScheduledRender();
    const nextDelay = drawScene(renderer.paused ? renderer.pausedAt : performance.now());
    if (Number.isFinite(nextDelay)) {
      scheduleRender(nextDelay);
    }
  } else {
    scheduleRender(0);
    void Promise.all(sourceUrls.map((sourceUrl) => ensureSourceReady(sourceUrl)))
      .catch((error) => {
        postError("upsert-source", error, message);
      });
  }
  postAck("upsert", message, {
    recordIds: normalized.map((record) => record.id),
    presented: sceneSourcesReady,
  });
}

function handleRemove(message) {
  const revision = getDeltaRevision(message);
  if (revision === null) {
    return;
  }
  const ids = Array.isArray(message.ids) ? message.ids : message.id != null ? [message.id] : [];
  const keys = new Set(ids.map((id) => getRecordKey(normalizeRecordId(id))));
  for (const key of keys) {
    renderer.records.delete(key);
  }
  renderer.order = renderer.order.filter((key) => !keys.has(key));
  invalidateSourceUsageCache();
  renderer.revision = revision;
  renderer.sceneGeneration += 1;
  pruneUnusedSources();
  scheduleSourceMaintenance();
  scheduleRender(0);
  postAck("remove", message, { removedCount: keys.size });
}

function handleOrder(message) {
  const revision = getDeltaRevision(message);
  if (revision === null) {
    return;
  }
  if (!Array.isArray(message.ids)) {
    throw new SceneRenderError("INVALID_ORDER", "order.ids must contain every current record id.");
  }
  const keys = message.ids.map((id) => getRecordKey(normalizeRecordId(id)));
  if (new Set(keys).size !== keys.length) {
    throw new SceneRenderError("INVALID_ORDER", "order.ids cannot contain duplicates.");
  }
  if (keys.length !== renderer.records.size || keys.some((key) => !renderer.records.has(key))) {
    throw new SceneRenderError("INVALID_ORDER", "order.ids must contain every current record exactly once.");
  }
  renderer.order = keys;
  renderer.revision = revision;
  renderer.sceneGeneration += 1;
  scheduleRender(0);
  postAck("order", message);
}

function handleCamera(message) {
  renderer.camera = normalizeCamera(message.camera);
  invalidateSourceUsageCache();
  scheduleSourceMaintenance();
  scheduleRender(0);
  postAck("camera", message);
}

function handleResize(message) {
  const width = Number(message.width);
  const height = Number(message.height);
  if (!Number.isFinite(width) || width <= 0 || !Number.isFinite(height) || height <= 0) {
    throw new SceneRenderError("INVALID_SIZE", "resize width and height must be positive.");
  }
  renderer.width = width;
  renderer.height = height;
  renderer.dpr = clamp(finitePositive(message.dpr, renderer.dpr), 0.25, MAX_DPR);
  invalidateSourceUsageCache();
  resizeBackingCanvas();
  scheduleSourceMaintenance();
  scheduleRender(0);
  postAck("resize", message, {
    width: renderer.width,
    height: renderer.height,
    dpr: renderer.dpr,
  });
}

function handlePause(message) {
  const paused = message.paused === true;
  const now = normalizeClientTimestamp(message.now, performance.now());
  if (paused && !renderer.paused) {
    renderer.paused = true;
    renderer.pausedAt = now;
    cancelScheduledRender();
    scheduleRender(0);
  } else if (!paused && renderer.paused) {
    const pauseStartedAt = renderer.pausedAt;
    for (const record of renderer.records.values()) {
      record.startedAt += Math.max(0, now - Math.max(pauseStartedAt, record.insertedAt));
      if (record.animationPaused && record.animationPausedAt != null) {
        record.animationPausedAt += Math.max(0, now - pauseStartedAt);
      }
    }
    renderer.paused = false;
    renderer.pausedAt = 0;
    scheduleRender(0);
  }
  postAck("pause", message, { paused: renderer.paused });
}

function handleDispose(message) {
  renderer.disposed = true;
  cancelScheduledRender();
  if (renderer.sourceMaintenanceTimerId !== null) {
    clearTimeout(renderer.sourceMaintenanceTimerId);
    renderer.sourceMaintenanceTimerId = null;
  }
  for (const source of sourceCache.values()) {
    if (source.status === "ready") {
      closeSourceData(source.data);
    }
  }
  sourceCache.clear();
  renderer.records.clear();
  renderer.order = [];
  invalidateSourceUsageCache();
  renderer.canvas = null;
  renderer.context = null;
  postMessage("disposed", {
    ...(message.requestId != null ? { requestId: message.requestId } : {}),
  });
  setTimeout(() => workerScope?.close?.(), 0);
}

function handleInit(message) {
  if (renderer.initialized) {
    throw new SceneRenderError("ALREADY_INITIALIZED", "The scene renderer is already initialized.");
  }
  const canvas = message.canvas;
  if (!canvas || typeof canvas.getContext !== "function") {
    throw new SceneRenderError(
      "OFFSCREEN_CANVAS_UNAVAILABLE",
      "init.canvas must be a transferred OffscreenCanvas.",
      { capability: true }
    );
  }
  if (typeof createImageBitmap !== "function") {
    throw new SceneRenderError(
      "CREATE_IMAGE_BITMAP_UNAVAILABLE",
      "createImageBitmap is required by the accelerated renderer.",
      { capability: true }
    );
  }
  if (
    typeof OffscreenCanvas !== "function" ||
    typeof fetch !== "function" ||
    typeof Blob !== "function" ||
    typeof TextDecoder !== "function"
  ) {
    throw new SceneRenderError(
      "WORKER_IMAGE_PIPELINE_UNAVAILABLE",
      "Required worker image and fetch APIs are unavailable.",
      {
        capability: true,
        details: {
          offscreenCanvas: typeof OffscreenCanvas === "function",
          fetch: typeof fetch === "function",
          blob: typeof Blob === "function",
          textDecoder: typeof TextDecoder === "function",
        },
      }
    );
  }
  const context = canvas.getContext("2d", { alpha: true, desynchronized: true });
  if (!context) {
    throw new SceneRenderError(
      "OFFSCREEN_2D_UNAVAILABLE",
      "A Canvas2D context could not be created from the transferred canvas.",
      { capability: true }
    );
  }

  const width = Number(message.width);
  const height = Number(message.height);
  if (!Number.isFinite(width) || width <= 0 || !Number.isFinite(height) || height <= 0) {
    throw new SceneRenderError("INVALID_SIZE", "init width and height must be positive CSS pixels.");
  }
  renderer.canvas = canvas;
  renderer.context = context;
  renderer.width = width;
  renderer.height = height;
  renderer.dpr = clamp(finitePositive(message.dpr, 1), 0.25, MAX_DPR);
  const clientTimeOrigin = Number(message.timeOrigin);
  const clientNow = Number(message.now);
  if (Number.isFinite(clientTimeOrigin)) {
    renderer.clientClockOffsetMs = clientTimeOrigin - performance.timeOrigin;
  } else if (Number.isFinite(clientNow)) {
    renderer.clientClockOffsetMs = performance.now() - clientNow;
  } else {
    renderer.clientClockOffsetMs = 0;
  }
  renderer.camera = normalizeCamera(message.camera || { x: 0, y: 0, scale: 1 });
  renderer.maxSourceBytes = clamp(
    Math.round(finitePositive(message.options?.maxSourceBytes, DEFAULT_MAX_SOURCE_BYTES)),
    1024,
    512 * 1024 * 1024
  );
  renderer.memoryBudgetBytes = clamp(
    Math.round(finitePositive(message.options?.memoryBudgetBytes, getDefaultMemoryBudget())),
    MIN_MEMORY_BUDGET_BYTES,
    MAX_MEMORY_BUDGET_BYTES
  );
  const hardwareConcurrency = finitePositive(workerScope?.navigator?.hardwareConcurrency, 4);
  const decodeConcurrency = clamp(
    Math.floor(finitePositive(message.options?.decodeConcurrency, Math.floor(hardwareConcurrency / 2))),
    1,
    4
  );
  renderer.sourceQueue = new WorkQueue(decodeConcurrency);
  renderer.capabilities = probeCapabilities(context);
  renderer.initialized = true;
  resizeBackingCanvas();
  scheduleRender(0);

  postMessage("initialized", {
    ...(message.requestId != null ? { requestId: message.requestId } : {}),
    width: renderer.width,
    height: renderer.height,
    dpr: renderer.dpr,
    camera: renderer.camera,
    capabilities: renderer.capabilities,
    memoryBudgetBytes: renderer.memoryBudgetBytes,
    decodeConcurrency,
    workerTimeOrigin: performance.timeOrigin,
    clientClockOffsetMs: renderer.clientClockOffsetMs,
  });
}

async function dispatchMessage(message) {
  if (message?.protocol !== SCENE_RENDER_PROTOCOL) {
    throw new SceneRenderError(
      "INVALID_PROTOCOL",
      `Expected protocol \"${SCENE_RENDER_PROTOCOL}\".`
    );
  }
  if (message?.version !== SCENE_RENDER_VERSION) {
    throw new SceneRenderError(
      "UNSUPPORTED_VERSION",
      `Scene renderer protocol version ${String(message?.version)} is unsupported.`,
      { capability: true, details: { supportedVersion: SCENE_RENDER_VERSION } }
    );
  }
  if (message.type === "init") {
    handleInit(message);
    return;
  }
  if (!renderer.initialized) {
    throw new SceneRenderError("NOT_INITIALIZED", "Send init before other renderer messages.");
  }
  if (renderer.disposed) {
    throw new SceneRenderError("RENDERER_DISPOSED", "The renderer has been disposed.");
  }

  switch (message.type) {
    case "scene":
      await handleScene(message);
      break;
    case "upsert":
      handleUpsert(message);
      break;
    case "remove":
      handleRemove(message);
      break;
    case "order":
      handleOrder(message);
      break;
    case "camera":
      handleCamera(message);
      break;
    case "resize":
      handleResize(message);
      break;
    case "pause":
      handlePause(message);
      break;
    case "dispose":
      handleDispose(message);
      break;
    case "memory-stats":
      postMemoryStats("requested");
      break;
    default:
      throw new SceneRenderError(
        "INVALID_MESSAGE_TYPE",
        `Unknown scene renderer message type \"${String(message.type)}\".`
      );
  }
}

workerScope?.addEventListener("message", (event) => {
  const message = event?.data;
  Promise.resolve(dispatchMessage(message)).catch((error) => {
    postError(message?.type || "unknown", error, message);
  });
});
