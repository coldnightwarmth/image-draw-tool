import { PHOTO_EXPORT_MEMORY_PROFILE, MAX_PHOTO_EXPORT_MEMORY_BYTES } from "../raster-memory-budget.mjs?v=20261009-photo-memory-v2";

const protocol = "brush-export-raster";
const hexColor = rgb => '#' + rgb.map(value => Math.max(0, Math.min(255, Math.round(value))).toString(16).padStart(2, '0')).join('');
export const abortError = () => new DOMException("Cancelled", "AbortError");

// One worker owns each preview/export. Termination also aborts outstanding
// network requests and discards decoder canvases when a composition changes.
export class RasterSession {
  constructor({ signal, progress = () => {} } = {}) {
    this.pending = new Map();
    this.nextId = 0;
    this.progress = progress;
    this.signal = signal;
    this.worker = new Worker(new URL("../export-raster-worker.js?v=20261009-photo-memory-v2", import.meta.url), { type: "module" });
    this.worker.onmessage = ({ data }) => {
      const request = this.pending.get(data.requestId);
      if (!request) { data.output?.bitmap?.close(); return; }
      if (data.type === "progress") { request.touch(); this.progress(data); return; }
      clearTimeout(request.timer);
      this.pending.delete(data.requestId);
      if (data.type === "error") request.reject(Object.assign(new Error(data.error?.message || "Image rendering failed."), { code: data.error?.code, details: data.error?.details }));
      else request.resolve(data);
    };
    this.worker.onerror = () => this.close(new Error("The image renderer stopped. Please try again."));
    this.worker.onmessageerror = () => this.close(new Error("The image renderer returned unreadable data."));
    this.onAbort = () => this.close();
    signal?.addEventListener("abort", this.onAbort, { once: true });
    if (signal?.aborted) this.close();
  }
  request(type, payload = {}) {
    if (this.closed) return Promise.reject(abortError());
    return new Promise((resolve, reject) => {
      const requestId = ++this.nextId;
      const request = { resolve, reject, touch: () => {
        clearTimeout(request.timer);
        request.timer = setTimeout(() => this.close(new Error("The renderer stopped responding. Try a smaller export or fewer images.")), 120000);
      } };
      request.touch();
      this.pending.set(requestId, request);
      this.worker.postMessage({ protocol, version: 1, type, requestId, jobId: "photo", ...payload });
    });
  }
  prepare(scene) { return this.request("prepare", { scene }); }
  async frame(timeMs = 0, output = "bitmap") { return (await this.request("render-frame", { timeMs, output })).output; }
  close(error = abortError()) {
    if (this.closed) return;
    this.closed = true;
    this.signal?.removeEventListener("abort", this.onAbort);
    this.worker.terminate();
    for (const request of this.pending.values()) { clearTimeout(request.timer); request.reject(error); }
    this.pending.clear();
  }
}

export function createScene(composition, catalog, width, height, { quality = true } = {}) {
  const { entries, background, referenceWidth: w, referenceHeight: h } = composition;
  const used = new Set(entries.map(entry => entry.assetId));
  const color = hexColor(background);
  return {
    quality, cacheRepeatedSources: quality, skipFailedFetches: true,
    outputWidth: width, outputHeight: height,
    memoryProfile: quality ? PHOTO_EXPORT_MEMORY_PROFILE : undefined,
    memoryBudgetBytes: quality ? MAX_PHOTO_EXPORT_MEMORY_BYTES : Math.min(384, Math.max(192, (navigator.deviceMemory || 4) * 64)) * 1024 * 1024,
    selectionBounds: { left: 0, top: 0, right: w, bottom: h },
    background: { include: true, color, matteColor: color },
    assets: [...used].map(id => {
      const asset = catalog.get(id);
      if (!asset) throw new Error("One of this composition’s images is no longer available.");
      return { id, url: asset.url, kind: asset.frames > 1 || asset.mimeType === "image/gif" || /\.gif$/i.test(asset.source) ? "gif" : "static",
        mimeType: asset.mimeType, targetWidth: quality ? asset.width : 0, targetHeight: quality ? asset.height : 0 };
    }),
    entries: entries.map(entry => {
      const asset = catalog.get(entry.assetId), span = entry.size * Math.min(w, h), longest = Math.max(asset.width, asset.height);
      return { sourceId: entry.assetId, centerX: entry.x * w, centerY: entry.y * h,
        width: span * asset.width / longest, height: span * asset.height / longest,
        rotation: entry.rotation, opacity: entry.opacity, blendMode: "normal", imageRendering: "auto",
        phaseOffsetMs: entry.phase || 0, playbackRate: 1,
        tintLayers: entry.tintAmount > 0 ? [{ color: hexColor(entry.tint), amountPercent: entry.tintAmount * 100 }] : [] };
    })
  };
}
