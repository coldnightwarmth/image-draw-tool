import { RasterSession, createScene, abortError } from "./raster-client.mjs?v=20261009-photo-memory-v2";
import { createQualityMp4Target } from "../generator/quality-mp4-target.mjs?v=20261005-quality-speed-v1";

const fourCC = (bytes, offset) => String.fromCharCode(...bytes.subarray(offset, offset + 4));
const writeCC = (bytes, offset, value) => [...value].forEach((char, i) => { bytes[offset + i] = char.charCodeAt(0); });
const uint24 = (bytes, offset, value) => { for (let i = 0; i < 3; i++) bytes[offset + i] = value >>> (i * 8) & 255; };
function chunk(type, parts, length) {
  const header = new Uint8Array(8); writeCC(header, 0, type);
  new DataView(header.buffer).setUint32(4, length, true);
  return new Blob([header, ...parts, ...(length % 2 ? [new Uint8Array(1)] : [])]);
}
async function webpFrame(blob, width, height, duration) {
  const bytes = new Uint8Array(await blob.arrayBuffer());
  if (fourCC(bytes, 0) !== "RIFF" || fourCC(bytes, 8) !== "WEBP") throw new Error("Invalid WebP frame.");
  const header = new Uint8Array(16); uint24(header, 6, width - 1); uint24(header, 9, height - 1); uint24(header, 12, duration); header[15] = 2;
  for (let at = 12; at + 8 <= bytes.length;) {
    const size = new DataView(bytes.buffer).getUint32(at + 4, true), end = at + 8 + size + size % 2;
    if (end > bytes.length) throw new Error("Incomplete WebP frame.");
    if (fourCC(bytes, at) === "VP8L") return chunk("ANMF", [header, bytes.subarray(at, end)], 16 + end - at);
    at = end;
  }
  throw new Error("The lossless WebP encoder did not return an image.");
}
function animatedWebp(frames, width, height, background) {
  const extended = new Uint8Array(10); extended[0] = 2;
  uint24(extended, 4, width - 1); uint24(extended, 7, height - 1);
  const [r, g, b] = background;
  const parts = [chunk("VP8X", [extended], 10), chunk("ANIM", [new Uint8Array([b, g, r, 255, 0, 0])], 6), ...frames];
  const size = 4 + parts.reduce((sum, part) => sum + part.size, 0);
  if (size > 0xffffffff) throw new Error("This animation exceeds WebP’s 4 GB limit. Use a shorter duration or smaller width.");
  const header = new Uint8Array(12); writeCC(header, 0, "RIFF"); writeCC(header, 8, "WEBP");
  new DataView(header.buffer).setUint32(4, size, true);
  return new Blob([header, ...parts], { type: "image/webp" });
}

export async function qualityEncoderConfig(width, height) {
  if (!globalThis.VideoEncoder || !globalThis.VideoFrame) throw new Error("MP4 export needs a browser with WebCodecs, such as current Chrome or Edge. PNG and WebP are also available.");
  const common = { width, height, framerate: 60, latencyMode: "quality", avc: { format: "avc" } };
  const requested = Math.max(64e6, width * height * 60 * 4);
  for (const bitrateMode of ["quantizer", "variable"]) for (const codec of ["avc1.640034", "avc1.640033", "avc1.4d0034", "avc1.420034"]) {
    const bitrates = bitrateMode === "quantizer" ? [null] : [...new Set([Math.min(requested, codec.startsWith("avc1.64") ? 300e6 : 240e6), Math.min(requested, 240e6)])];
    for (const bitrate of bitrates) for (const hardwareAcceleration of ["prefer-software", "no-preference"]) {
      const config = { ...common, codec, bitrateMode, hardwareAcceleration, ...(bitrate ? { bitrate } : {}) };
      try {
        const support = await VideoEncoder.isConfigSupported(config);
        if (support.supported && support.config.bitrateMode === bitrateMode) return support.config;
      } catch { /* Try the next supported H.264 profile. */ }
    }
  }
  throw new Error("This browser cannot encode MP4 at these dimensions. Try a smaller width, or choose WebP.");
}

export async function renderExport(composition, catalog, { format = "mp4", width = 1200, seconds = 6, timeMs = 0, signal, progress = () => {} } = {}) {
  width = Math.max(64, Math.min(2400, Math.round(Number(width) || 1200)));
  let height = Math.max(1, Math.round(width * composition.referenceHeight / composition.referenceWidth));
  // Cap the long side as well, including very tall references.
  if (height > 2400) { width = Math.max(1, Math.round(width * 2400 / height)); height = 2400; }
  if (!["png", "webp", "mp4"].includes(format)) throw new Error("Unknown export format.");
  seconds = Math.max(1, Math.min(15, Number(seconds) || 6));
  const check = () => { if (signal?.aborted) throw abortError(); };
  check();
  let encoder, encoderFailure, muxer, target, config;
  const session = new RasterSession({ signal, progress: message => {
    if (message.phase === "assets") progress({ fraction: .15 * message.completed / Math.max(1, message.total), text: `loading images ${message.completed}/${message.total}` });
  } });
  try {
    if (format === "mp4") {
      const encodedWidth = Math.ceil(width / 2) * 2, encodedHeight = Math.ceil(height / 2) * 2;
      config = await qualityEncoderConfig(encodedWidth, encodedHeight); check();
      const { Muxer, StreamTarget } = await import("../generator/vendor/mp4-muxer.mjs");
      target = createQualityMp4Target(StreamTarget);
      muxer = new Muxer({ target: target.target, video: { codec: "avc", width: encodedWidth, height: encodedHeight, frameRate: 60 }, fastStart: false });
      encoder = new VideoEncoder({ output: (chunk, metadata) => muxer.addVideoChunk(chunk, metadata), error: error => { encoderFailure = error; } });
      encoder.configure(config);
    }
    progress({ fraction: 0, text: "preparing full-quality images" });
    const prepared = await session.prepare(createScene(composition, catalog, width, height)); check();
    const skipped = prepared.skippedAssets?.length || 0;
    if (format === "png") {
      const output = await session.frame(timeMs, "png"); check();
      progress({ fraction: 1, text: "ready" });
      return { blob: output.blob, width, height, skipped, format };
    }
    const fps = format === "webp" ? 50 : 60, count = Math.round(seconds * fps), frames = [];
    const canvas = format === "mp4" ? new OffscreenCanvas(config.width, config.height) : null, context = canvas?.getContext("2d", { alpha: false });
    if (context) { context.fillStyle = `rgb(${composition.background.join(",")})`; context.fillRect(0, 0, canvas.width, canvas.height); }
    const waitForEncoder = async operation => {
      let timer, abort;
      try {
        await Promise.race([operation, new Promise((_, reject) => {
          timer = setTimeout(() => reject(new Error("The video encoder stopped responding. Try WebP or a smaller width.")), 60000);
          abort = () => reject(abortError()); signal?.addEventListener("abort", abort, { once: true });
          if (signal?.aborted) abort();
        })]);
      } finally { clearTimeout(timer); signal?.removeEventListener("abort", abort); }
    };
    for (let index = 0; index < count; index++) {
      check(); if (encoderFailure) throw encoderFailure;
      const output = await session.frame(index * 1000 / fps, format === "webp" ? "webp" : "bitmap");
      if (format === "webp") frames.push(await webpFrame(output.blob, width, height, 1000 / fps));
      else {
        try { check(); context.drawImage(output.bitmap, 0, 0); } finally { output.bitmap.close(); }
        const timestamp = Math.round(index * 1e6 / fps), duration = Math.round((index + 1) * 1e6 / fps) - timestamp;
        const frame = new VideoFrame(canvas, { timestamp, duration });
        try { encoder.encode(frame, { keyFrame: index % fps === 0, ...(config.bitrateMode === "quantizer" ? { avc: { quantizer: 0 } } : {}) }); }
        finally { frame.close(); }
        // Flush a bounded batch: backpressure and errors cannot retain an
        // unbounded queue of high-resolution VideoFrames.
        if (encoder.encodeQueueSize > 6) await waitForEncoder(encoder.flush());
      }
      progress({ fraction: .15 + .84 * (index + 1) / count, text: `rendering ${index + 1}/${count} frames` });
    }
    check();
    let blob;
    if (encoder) { await waitForEncoder(encoder.flush()); check(); if (encoderFailure) throw encoderFailure; muxer.finalize(); blob = target.finish(); }
    else blob = animatedWebp(frames, width, height, composition.background);
    progress({ fraction: 1, text: "ready" });
    return { blob, width: canvas?.width || width, height: canvas?.height || height, skipped, format, fps, frameCount: count, seconds };
  } finally { session.close(); if (encoder && encoder.state !== "closed") encoder.close(); }
}
