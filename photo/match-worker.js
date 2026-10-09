import { fitCollage, describePixels, normalizeSettings } from "./matcher.mjs?v=20261009-photo-v1";
import { QualityGifDecoder } from "../generator/quality-gif-decoder.mjs?v=20261005-quality-speed-v1";

const TILE_SIZE = 32;
const localAssets = new Map();
let stockPromise, generation = 0, importGeneration = 0, pendingImport = null;
const pause = () => globalThis.scheduler?.yield ? scheduler.yield() : new Promise(resolve => setTimeout(resolve, 0));

function metadata(asset) {
  const { pixels, tileSize, ...info } = asset;
  return info;
}

async function stock() {
  stockPromise ||= (async () => {
    const response = await fetch("./data/stock-index.json?v=20261009-photo-v1");
    if (!response.ok) throw new Error("The stock asset index could not be loaded. Try again.");
    const manifest = await response.json();
    const atlasResponse = await fetch(`./data/${manifest.atlas}?v=20261009-photo-v1`);
    if (!atlasResponse.ok) throw new Error("The stock asset thumbnails could not be loaded.");
    const bitmap = await createImageBitmap(await atlasResponse.blob());
    const canvas = new OffscreenCanvas(manifest.tileSize, manifest.tileSize), context = canvas.getContext("2d", { willReadFrequently: true });
    try {
      return manifest.assets.map((asset, index) => {
        context.clearRect(0, 0, manifest.tileSize, manifest.tileSize);
        context.drawImage(bitmap, index % manifest.columns * manifest.tileSize, Math.floor(index / manifest.columns) * manifest.tileSize,
          manifest.tileSize, manifest.tileSize, 0, 0, manifest.tileSize, manifest.tileSize);
        return { ...asset, id: asset.source, type: "stock", tileSize: manifest.tileSize,
          pixels: context.getImageData(0, 0, manifest.tileSize, manifest.tileSize).data };
      });
    } finally { bitmap.close(); canvas.width = canvas.height = 1; }
  })().catch(error => { stockPromise = null; throw error; });
  return stockPromise;
}

function sampleImage(image, width, height) {
  const canvas = new OffscreenCanvas(TILE_SIZE, TILE_SIZE), context = canvas.getContext("2d", { willReadFrequently: true });
  const scale = TILE_SIZE / Math.max(width, height), w = Math.max(1, Math.round(width * scale)), h = Math.max(1, Math.round(height * scale));
  context.drawImage(image, Math.floor((TILE_SIZE - w) / 2), Math.floor((TILE_SIZE - h) / 2), w, h);
  return context.getImageData(0, 0, TILE_SIZE, TILE_SIZE).data;
}

async function analyzeFile(item, cancelled) {
  const { file } = item;
  if (file.size > 64 * 1024 * 1024) throw new Error("file exceeds 64 MB");
  const bytes = await file.arrayBuffer();
  if (cancelled()) throw new DOMException("Cancelled", "AbortError");
  const gif = new Uint8Array(bytes, 0, Math.min(bytes.byteLength, 6));
  const isGif = String.fromCharCode(...gif).startsWith("GIF8");
  let pixels, width, height, frames = 1, phase = 0, duration = 0, temporalMean;
  if (isGif) {
    let allocated = 0;
    const budget = 192 * 1024 * 1024;
    const check = () => { if (cancelled()) throw new DOMException("Cancelled", "AbortError"); };
    const decoder = new QualityGifDecoder({
      reserve: bytes => { while (allocated + bytes > budget && decoder.evictOne()) { /* free cached frames */ }
        if (allocated + bytes > budget) throw new Error("GIF exceeds the analysis memory budget"); allocated += bytes; },
      release: bytes => { allocated -= bytes; }, availableBytes: () => budget - allocated, frameCacheLimit: budget / 4,
      check, yieldWork: pause, byteLength: (w, h) => { if (!(w > 0 && h > 0) || w * h > 32e6) throw new Error("image dimensions are too large"); return w * h * 4; },
      frameDelay: frame => frame.gce ? Math.max(20, frame.gce.delay > 0 ? frame.gce.delay * 10 : 100) : 50,
      backgroundColor: (parsed, raw) => {
        if (raw.some(frame => frame.gce?.extras.transparentColorGiven)) return "";
        const rgb = parsed.gct?.[parsed.lsd.backgroundColorIndex]; return rgb ? `rgb(${rgb.join(",")})` : "";
      }
    });
    try {
      const asset = decoder.prepare(bytes, item.id);
      ({ width, height } = asset); frames = asset.frames.length; duration = asset.totalDurationMs;
      const samples = [];
      for (const fraction of frames > 1 ? [0, .25, .5, .75] : [0]) {
        check();
        const time = Math.floor(fraction * duration), source = await decoder.resolve(asset, time);
        const rgba = sampleImage(source, width, height); decoder.pinned = null;
        const description = describePixels(rgba, TILE_SIZE);
        if (description.coverage > .008) samples.push({ pixels: rgba, phase: time, ...description });
        await pause();
      }
      if (!samples.length) throw new Error("image is completely transparent");
      const coverage = samples.reduce((sum, s) => sum + s.coverage, 0);
      temporalMean = [0, 1, 2].map(c => samples.reduce((sum, s) => sum + s.mean[c] * s.coverage, 0) / coverage);
      samples.sort((a, b) => a.mean.reduce((sum, v, c) => sum + (v - temporalMean[c]) ** 2, 0) - b.mean.reduce((sum, v, c) => sum + (v - temporalMean[c]) ** 2, 0));
      ({ pixels, phase } = samples[0]);
    } finally { decoder.clear(); }
  } else {
    const bitmap = await createImageBitmap(new Blob([bytes], { type: file.type }));
    try {
      width = bitmap.width; height = bitmap.height;
      if (width * height > 32e6) throw new Error("image exceeds 32 megapixels");
      pixels = sampleImage(bitmap, width, height);
    } finally { bitmap.close(); }
  }
  const description = describePixels(pixels, TILE_SIZE);
  if (description.coverage < .008) throw new Error("image is completely transparent");
  return { id: item.id, source: item.source, name: file.name, category: "local", type: "local",
    width, height, frames, phase, duration, mimeType: isGif ? "image/gif" : file.type,
    tileSize: TILE_SIZE, pixels, ...description, temporalMean: temporalMean || description.mean };
}

function postPreview(id, result, final = false) {
  const canvas = new OffscreenCanvas(result.width, result.height);
  canvas.getContext("2d").putImageData(new ImageData(result.pixels, result.width, result.height), 0, 0);
  const bitmap = canvas.transferToImageBitmap();
  const { pixels, ...rest } = result;
  postMessage({ type: final ? "fitted" : "progress", id, ...rest, bitmap }, [bitmap]);
}

self.addEventListener("message", async ({ data: message }) => {
  const { type, id } = message;
  try {
    if (type === "init") {
      const assets = await stock();
      postMessage({ type: "catalog", id, assets: assets.map(metadata) });
    } else if (type === "cancel") {
      generation++; importGeneration++; pendingImport = null;
    } else if (type === "commit-import") {
      if (pendingImport?.id === id) {
        localAssets.clear();
        for (const asset of pendingImport.assets) localAssets.set(asset.id, asset);
        pendingImport = null;
      }
    } else if (type === "import") {
      const token = ++importGeneration;
      generation++;
      const results = [], failures = [];
      for (const [index, item] of message.items.entries()) {
        if (token !== importGeneration) return;
        try { results.push(await analyzeFile(item, () => token !== importGeneration)); }
        catch (error) { if (error.name === "AbortError") return; failures.push({ name: item.file.name, reason: error.message }); }
        postMessage({ type: "import-progress", id, completed: index + 1, total: message.items.length });
        await pause();
      }
      if (token !== importGeneration) return;
      // Keep the previous folder until the UI accepts this particular result.
      // A stop/new import can race with an already-posted completion message.
      pendingImport = { id, assets: results };
      postMessage({ type: "imported", id, assets: results.map(metadata), failures });
    } else if (type === "fit") {
      const token = ++generation;
      const settings = normalizeSettings(message.settings);
      const all = message.sourceMode === "local" ? [] : await stock();
      if (token !== generation) return;
      const categories = new Set(message.categories || []);
      const assets = [...all.filter(asset => categories.has(asset.category)),
        ...(message.sourceMode === "stock" ? [] : localAssets.values())];
      const result = await fitCollage({ ...message, settings, assets }, {
        cancelled: () => token !== generation,
        yieldWork: pause,
        progress: progress => { if (token === generation) postPreview(id, progress); }
      });
      if (token === generation) postPreview(id, result, true);
    }
  } catch (error) {
    if (error.name !== "AbortError") postMessage({ type: "error", id, message: error.message || "Image matching failed." });
  }
});
