import { decompressFrame, parseGIF } from "../gifuct-js.bundle.mjs";

// Keep compressed sources and a bounded LRU of native-resolution compositors.
// Eviction costs decoding time, never pixels or source animation frames.
export class QualityGifDecoder {
  constructor({ reserve, release, check, yieldWork, backgroundColor, frameDelay, byteLength }) {
    Object.assign(this, { reserve, release, check, yieldWork, backgroundColor, frameDelay, byteLength });
    this.cache = new Map();
    this.pinned = null;
  }

  prepare(bytes, id) {
    const parsed = parseGIF(bytes);
    const rawFrames = parsed.frames.filter(frame => frame.image);
    if (!rawFrames.length || rawFrames.length > 20000) throw new Error("Invalid GIF frame count.");
    const width = Number(parsed.lsd.width), height = Number(parsed.lsd.height);
    const frameBytes = this.byteLength(width, height);
    let maxPatchBytes = 0;
    for (const { image: { descriptor } } of rawFrames) {
      maxPatchBytes = Math.max(maxPatchBytes, this.byteLength(descriptor.width, descriptor.height));
    }
    // Account for the compressed input and parser structures as well as canvases.
    this.reserve(bytes.byteLength * 2 + rawFrames.length * 256);
    const frames = rawFrames.map(frame => ({ durationMs: this.frameDelay(frame) }));
    return {
      id, kind: "gif", quality: true, width, height, frames, rawFrames, parsed,
      totalDurationMs: frames.reduce((sum, frame) => sum + frame.durationMs, 0),
      background: this.backgroundColor(parsed, rawFrames),
      // Composite/restore canvases, patch canvas/RGBA and GIFuct pixel arrays.
      workingBytes: frameBytes * 2 + maxPatchBytes * 4,
      targetWidth: width, targetHeight: height,
      originalFrameCount: frames.length
    };
  }

  evictOne() {
    for (const [id, state] of this.cache) {
      if (id === this.pinned) continue;
      state.canvas.width = state.patch.width = 1;
      state.canvas.height = state.patch.height = 1;
      state.restore = null;
      this.cache.delete(id);
      this.release(state.bytes);
      return true;
    }
    return false;
  }

  clear() {
    this.pinned = null;
    while (this.evictOne()) { /* close all retained compositors */ }
  }

  async resolve(asset, timeMs, phaseOffsetMs = 0, playbackRate = 1) {
    this.check();
    let time = playbackRate > 0
      ? ((timeMs * playbackRate + phaseOffsetMs) % asset.totalDurationMs + asset.totalDurationMs) % asset.totalDurationMs
      : 0;
    let target = 0;
    while (target < asset.frames.length - 1 && time >= asset.frames[target].durationMs) {
      time -= asset.frames[target++].durationMs;
    }
    let state = this.cache.get(asset.id);
    if (!state) {
      this.reserve(asset.workingBytes);
      try {
        const canvas = new OffscreenCanvas(asset.width, asset.height);
        const patch = new OffscreenCanvas(1, 1);
        const context = canvas.getContext("2d", { willReadFrequently: true });
        if (!context) throw new Error("Could not create quality GIF compositor.");
        state = { canvas, context, patch, index: -1, previous: null, restore: null, bytes: asset.workingBytes };
      } catch (error) {
        this.release(asset.workingBytes);
        throw error;
      }
    }
    this.cache.delete(asset.id);
    this.cache.set(asset.id, state);
    this.pinned = asset.id;
    try {
      if (state.index < 0 || target < state.index) {
        state.context.clearRect(0, 0, asset.width, asset.height);
        if (asset.background) {
          state.context.fillStyle = asset.background;
          state.context.fillRect(0, 0, asset.width, asset.height);
        }
        state.index = -1;
        state.previous = state.restore = null;
      }
      while (state.index < target) {
        this.check();
        const previous = state.previous;
        if (previous?.disposalType === 2) {
          const { left, top, width, height } = previous.dims;
          if (asset.background) {
            state.context.fillStyle = asset.background;
            state.context.fillRect(left, top, width, height);
          } else state.context.clearRect(left, top, width, height);
        } else if (previous?.disposalType === 3 && state.restore) {
          state.context.putImageData(state.restore, 0, 0);
        }
        state.restore = null;
        state.previous = null;
        const frame = decompressFrame(asset.rawFrames[state.index + 1], asset.parsed.gct, true);
        const { width, height, left, top } = frame.dims;
        if (frame.disposalType === 3) {
          state.restore = state.context.getImageData(0, 0, asset.width, asset.height);
        }
        state.patch.width = width;
        state.patch.height = height;
        state.patch.getContext("2d").putImageData(new ImageData(frame.patch, width, height), 0, 0);
        state.context.drawImage(state.patch, left, top);
        state.previous = { dims: frame.dims, disposalType: frame.disposalType };
        state.index++;
        if (state.index % 16 === 15) await this.yieldWork();
      }
      return state.canvas;
    } catch (error) {
      this.pinned = null;
      throw error;
    }
  }
}
