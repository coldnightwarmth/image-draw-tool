import { decompressFrame, parseGIF } from "../gifuct-js.bundle.mjs";

// Keep compressed sources and a bounded LRU of exact frames and compositors.
// Eviction costs decoding time, never pixels or source animation frames.
export class QualityGifDecoder {
  constructor({ reserve, release, check, yieldWork, backgroundColor, frameDelay, byteLength, availableBytes = () => 0, frameCacheLimit = 0 }) {
    Object.assign(this, { reserve, release, check, yieldWork, backgroundColor, frameDelay, byteLength, availableBytes, frameCacheLimit });
    this.frameCacheBytes = 0;
    this.stats = { decodedFrames: 0, cacheHits: 0, checkpoints: 0 };
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
    let elapsed = 0;
    const frames = rawFrames.map(frame => ({ durationMs: this.frameDelay(frame) }));
    const frameEnds = Float64Array.from(frames, frame => (elapsed += frame.durationMs));
    // A full opaque frame with no restore-previous disposal is independent of
    // earlier pixels. Index those safe seek points without decoding their LZW.
    let independent = -1;
    const seekStarts = Int32Array.from(rawFrames, (frame, index) => {
      const { left, top, width: patchWidth, height: patchHeight } = frame.image.descriptor;
      if (left === 0 && top === 0 && patchWidth === width && patchHeight === height &&
          !frame.gce?.extras.transparentColorGiven && frame.gce?.extras.disposal !== 3) independent = index;
      return independent;
    });
    return {
      id, kind: "gif", quality: true, width, height, frames, rawFrames, parsed, frameEnds, seekStarts,
      compositor: null, snapshots: new Map(), frameBytes: Math.max(4096, frameBytes),
      totalDurationMs: frames.reduce((sum, frame) => sum + frame.durationMs, 0),
      background: this.backgroundColor(parsed, rawFrames),
      // Composite/restore canvases, patch canvas/RGBA and GIFuct pixel arrays.
      workingBytes: frameBytes * 2 + maxPatchBytes * 4,
      targetWidth: width, targetHeight: height,
      originalFrameCount: frames.length
    };
  }

  touch(record) {
    this.cache.delete(record);
    this.cache.set(record, record);
  }

  evictOne(framesOnly = false) {
    for (const record of this.cache.values()) {
      if (record === this.pinned || (framesOnly && record.kind !== "frame")) continue;
      record.canvas.width = record.canvas.height = 1;
      if (record.kind === "frame") {
        record.asset.snapshots.delete(record.index);
        this.frameCacheBytes -= record.bytes;
      } else {
        record.patch.width = record.patch.height = 1;
        record.asset.compositor = null;
      }
      record.restore = null;
      this.cache.delete(record);
      this.release(record.bytes);
      return true;
    }
    return false;
  }

  remember(asset, state) {
    const bytes = asset.frameBytes * (state.restore ? 2 : 1);
    if (bytes > this.frameCacheLimit) return;
    while ((this.frameCacheBytes + bytes > this.frameCacheLimit || this.availableBytes() < bytes) && this.evictOne(true)) { /* recycle optional frames first */ }
    if (this.availableBytes() < bytes || this.frameCacheBytes + bytes > this.frameCacheLimit) return;
    this.reserve(bytes);
    let canvas;
    try {
      canvas = new OffscreenCanvas(asset.width, asset.height);
      const context = canvas.getContext("2d", { willReadFrequently: true });
      if (!context) throw new Error("Could not cache a quality GIF frame.");
      context.drawImage(state.canvas, 0, 0);
      const record = { kind: "frame", asset, index: state.index, canvas, bytes,
        previous: state.previous, restore: state.restore };
      asset.snapshots.set(state.index, record);
      this.frameCacheBytes += bytes;
      this.touch(record);
    } catch (error) {
      if (canvas) canvas.width = canvas.height = 1;
      this.release(bytes);
      throw error;
    }
  }

  frameIndex(asset, timeMs, phaseOffsetMs = 0, playbackRate = 1) {
    const time = playbackRate > 0
      ? ((timeMs * playbackRate + phaseOffsetMs) % asset.totalDurationMs + asset.totalDurationMs) % asset.totalDurationMs
      : 0;
    let low = 0, high = asset.frames.length - 1;
    while (low < high) {
      const mid = (low + high) >>> 1;
      if (time >= asset.frameEnds[mid]) low = mid + 1;
      else high = mid;
    }
    return low;
  }

  clear() {
    this.pinned = null;
    while (this.evictOne()) { /* close all retained compositors */ }
  }

  async resolve(asset, timeMs, phaseOffsetMs = 0, playbackRate = 1) {
    this.check();
    const target = this.frameIndex(asset, timeMs, phaseOffsetMs, playbackRate);
    const hit = asset.snapshots.get(target);
    if (hit) {
      this.touch(hit);
      this.pinned = hit;
      this.stats.cacheHits++;
      return hit.canvas;
    }
    let state = asset.compositor;
    if (!state) {
      this.reserve(asset.workingBytes);
      try {
        const canvas = new OffscreenCanvas(asset.width, asset.height);
        const patch = new OffscreenCanvas(1, 1);
        const context = canvas.getContext("2d", { willReadFrequently: true });
        if (!context) throw new Error("Could not create quality GIF compositor.");
        state = { kind: "compositor", asset, canvas, context, patch, index: -1, previous: null, restore: null, bytes: asset.workingBytes };
        asset.compositor = state;
      } catch (error) {
        this.release(asset.workingBytes);
        throw error;
      }
    }
    this.touch(state);
    this.pinned = state;
    try {
      // Saved display frames also carry disposal state, so a rewind can start
      // at the nearest exact checkpoint instead of frame zero.
      let checkpoint = null;
      for (const saved of asset.snapshots.values()) {
        if (saved.index < target && (target < state.index || saved.index > state.index) &&
            (!checkpoint || saved.index > checkpoint.index)) checkpoint = saved;
      }
      const seekStart = asset.seekStarts[target];
      if (seekStart >= 0 && (target < state.index || seekStart > state.index + 1) &&
          (!checkpoint || seekStart > checkpoint.index + 1)) {
        state.index = seekStart - 1;
        state.previous = state.restore = null;
      } else if (checkpoint) {
        state.context.globalCompositeOperation = "copy";
        state.context.drawImage(checkpoint.canvas, 0, 0);
        state.context.globalCompositeOperation = "source-over";
        state.index = checkpoint.index;
        state.previous = checkpoint.previous;
        state.restore = checkpoint.restore;
        this.touch(checkpoint);
        this.stats.checkpoints++;
      }
      if (state.index < 0 || target < state.index) {
        state.context.clearRect(0, 0, asset.width, asset.height);
        if (asset.background) {
          state.context.fillStyle = asset.background;
          state.context.fillRect(0, 0, asset.width, asset.height);
        }
        state.index = -1;
        state.previous = state.restore = null;
      }
      let yieldDeadline = performance.now() + 8;
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
        this.stats.decodedFrames++;
        const frame = decompressFrame(asset.rawFrames[state.index + 1], asset.parsed.gct, true);
        const { width, height, left, top } = frame.dims;
        if (frame.disposalType === 3) {
          state.restore = state.context.getImageData(0, 0, asset.width, asset.height);
        }
        if (state.patch.width !== width) state.patch.width = width;
        if (state.patch.height !== height) state.patch.height = height;
        state.patch.getContext("2d").putImageData(new ImageData(frame.patch, width, height), 0, 0);
        state.context.drawImage(state.patch, left, top);
        state.previous = { dims: frame.dims, disposalType: frame.disposalType };
        state.index++;
        if (performance.now() >= yieldDeadline) {
          await this.yieldWork();
          yieldDeadline = performance.now() + 8;
        }
      }
      if (!asset.snapshots.has(state.index)) this.remember(asset, state);
      return state.canvas;
    } catch (error) {
      this.pinned = null;
      throw error;
    }
  }
}
