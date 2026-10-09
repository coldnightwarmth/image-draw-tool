// The fitter only sees small asset samples. Its output is a list of original
// image placements; reference pixels are never used as a rendered layer.
export const DEFAULTS = Object.freeze({ resemblance: 55, count: 600, size: 12,
  variation: 80, overlap: 85, scatter: 35, rotation: 30, spill: 55,
  recolor: 35, transparency: 20, variety: 70, grid: false });

export const PRESETS = Object.freeze({
  loose: { ...DEFAULTS, resemblance: 25, count: 280, size: 18, scatter: 65, rotation: 65, spill: 85, recolor: 25 },
  balanced: DEFAULTS,
  detailed: { ...DEFAULTS, resemblance: 96, count: 3200, size: 4, variation: 45,
    overlap: 95, scatter: 5, rotation: 12, spill: 12, recolor: 85, transparency: 35, variety: 45 }
});

export const clamp = (value, low, high) => Math.max(low, Math.min(high, value));
export function normalizeSettings(raw = {}) {
  const result = {};
  for (const [key, fallback] of Object.entries(DEFAULTS)) {
    if (key === "grid") result.grid = raw.grid === true;
    else {
      const value = Number(raw[key] ?? fallback);
      result[key] = clamp(Number.isFinite(value) ? value : fallback,
        key === "count" ? 25 : key === "size" ? 1 : 0,
        key === "count" ? 8000 : key === "size" ? 40 : key === "rotation" ? 180 : 100);
    }
  }
  result.count = Math.round(result.count);
  return result;
}

function rng(seed) {
  let value = seed >>> 0;
  return () => {
    value += 0x6d2b79f5;
    let n = value;
    n = Math.imul(n ^ n >>> 15, n | 1);
    n ^= n + Math.imul(n ^ n >>> 7, n | 61);
    return ((n ^ n >>> 14) >>> 0) / 4294967296;
  };
}

export function describePixels(pixels, tileSize = 32) {
  let alpha = 0, red = 0, green = 0, blue = 0;
  for (let p = 0; p < pixels.length; p += 4) {
    const a = pixels[p + 3] / 255;
    alpha += a; red += pixels[p] * a; green += pixels[p + 1] * a; blue += pixels[p + 2] * a;
  }
  return { mean: alpha ? [red / alpha, green / alpha, blue / alpha] : [0, 0, 0],
    coverage: alpha / (tileSize * tileSize) };
}

function backgroundColor(target) {
  const bins = new Map();
  for (let p = 0; p < target.length; p += 4) {
    const key = ((target[p] >> 4) << 8) | ((target[p + 1] >> 4) << 4) | (target[p + 2] >> 4);
    const bin = bins.get(key) || [0, 0, 0, 0];
    bin[0]++; bin[1] += target[p]; bin[2] += target[p + 1]; bin[3] += target[p + 2]; bins.set(key, bin);
  }
  let winner = [1, 255, 255, 255];
  for (const bin of bins.values()) if (bin[0] > winner[0]) winner = bin;
  return winner.slice(1).map(value => Math.round(value / winner[0]));
}

function soften(input, width, height, radius) {
  let data = new Float32Array(input);
  for (let pass = 0; radius > 0 && pass < 2; pass++) {
    const next = new Float32Array(data.length);
    const horizontal = pass === 0;
    const rows = horizontal ? height : width, length = horizontal ? width : height;
    const at = (row, x) => (horizontal ? row * width + x : x * width + row) * 4;
    for (let row = 0; row < rows; row++) {
      const sums = [0, 0, 0];
      for (let x = -radius; x <= radius; x++) {
        const p = at(row, clamp(x, 0, length - 1));
        for (let c = 0; c < 3; c++) sums[c] += data[p + c];
      }
      for (let x = 0; x < length; x++) {
        const p = at(row, x), left = at(row, clamp(x - radius, 0, length - 1)), right = at(row, clamp(x + radius + 1, 0, length - 1));
        for (let c = 0; c < 3; c++) { next[p + c] = sums[c] / (radius * 2 + 1); sums[c] += data[right + c] - data[left + c]; }
        next[p + 3] = 255;
      }
    }
    data = next;
  }
  return data;
}

const weights = [0.3, 0.5, 0.2];
const colorDistance = (a, b) => weights.reduce((sum, weight, c) => sum + weight * (a[c] - b[c]) ** 2, 0);
export function imageError(actual, target) {
  let sum = 0;
  for (let p = 0; p < target.length; p += 4)
    for (let c = 0; c < 3; c++) sum += weights[c] * (actual[p + c] - target[p + c]) ** 2;
  return sum / (target.length / 4);
}

export async function fitCollage({ width, height, pixels, assets, settings: raw, seed = 1, initial = [], background },
  { progress = () => {}, cancelled = () => false, yieldWork = () => new Promise(resolve => setTimeout(resolve, 0)) } = {}) {
  const settings = normalizeSettings(raw);
  if (!assets.length) throw new Error("Choose at least one usable asset.");
  const random = rng(seed + initial.length * 31), shortSide = Math.min(width, height);
  const fidelity = settings.resemblance / 100, chaos = settings.scatter / 100;
  const target = soften(pixels, width, height, Math.round((1 - fidelity) ** 2 * shortSide * .055));
  const bg = background || backgroundColor(pixels);
  const canvas = new Float32Array(pixels.length), coverage = new Float32Array(width * height);
  for (let p = 0; p < canvas.length; p += 4) { canvas.set(bg, p); canvas[p + 3] = 255; }
  const entries = [], uses = new Map(), byId = new Map(assets.map(asset => [asset.id, asset]));
  const baseError = imageError(canvas, pixels);

  // Sampling a transformed thumbnail directly avoids allocating a canvas for
  // each search candidate. Only the pixels covered by that candidate are scored.
  function sample(entry, visit) {
    const asset = byId.get(entry.assetId);
    if (!asset) return;
    const size = entry.size * shortSide, centerX = entry.x * width, centerY = entry.y * height;
    const angle = entry.rotation * Math.PI / 180, cos = Math.cos(angle), sin = Math.sin(angle);
    const radius = size * (Math.abs(cos) + Math.abs(sin)) * .5;
    const left = Math.max(0, Math.floor(centerX - radius)), right = Math.min(width, Math.ceil(centerX + radius));
    const top = Math.max(0, Math.floor(centerY - radius)), bottom = Math.min(height, Math.ceil(centerY + radius));
    for (let y = top; y < bottom; y++) for (let x = left; x < right; x++) {
      const dx = (x + .5 - centerX) / size, dy = (y + .5 - centerY) / size;
      const u = cos * dx + sin * dy + .5, v = -sin * dx + cos * dy + .5;
      if (u < 0 || u >= 1 || v < 0 || v >= 1) continue;
      const at = (Math.floor(v * asset.tileSize) * asset.tileSize + Math.floor(u * asset.tileSize)) * 4;
      const alpha = asset.pixels[at + 3] / 255 * entry.opacity;
      if (alpha > .004) visit((y * width + x) * 4, at, alpha, asset);
    }
  }

  function apply(entry) {
    sample(entry, (p, at, alpha, asset) => {
      for (let c = 0; c < 3; c++) {
        const color = asset.pixels[at + c] * (1 - entry.tintAmount) + entry.tint[c] * entry.tintAmount;
        canvas[p + c] += (color - canvas[p + c]) * alpha;
      }
      coverage[p / 4] += alpha;
    });
    uses.set(entry.assetId, (uses.get(entry.assetId) || 0) + 1);
    entries.push(entry);
  }
  for (const entry of initial) if (byId.has(entry.assetId)) apply(entry);
  const initialError = imageError(canvas, pixels);

  function evaluate(entry, centerColor) {
    const tint = entry.tintAmount;
    if (tint > 0) {
      const sums = [0, 0, 0]; let denominator = 0;
      sample(entry, (p, at, alpha, asset) => {
        const k = alpha * tint;
        denominator += k * k;
        for (let c = 0; c < 3; c++) sums[c] += (target[p + c] - canvas[p + c] * (1 - alpha) - asset.pixels[at + c] * alpha * (1 - tint)) * k;
      });
      entry.tint = sums.map(value => Math.round(clamp(value / Math.max(denominator, .0001), 0, 255)));
    }
    let gain = 0, area = 0, overlapCost = 0, boundaryCost = 0;
    sample(entry, (p, at, alpha, asset) => {
      area += alpha;
      overlapCost += Math.min(coverage[p / 4], 4) * alpha;
      let edgeDifference = 0;
      for (let c = 0; c < 3; c++) {
        const color = asset.pixels[at + c] * (1 - tint) + entry.tint[c] * tint;
        const next = canvas[p + c] + (color - canvas[p + c]) * alpha;
        gain += weights[c] * ((canvas[p + c] - target[p + c]) ** 2 - (next - target[p + c]) ** 2);
        edgeDifference += weights[c] * (target[p + c] - centerColor[c]) ** 2;
      }
      boundaryCost += Math.max(0, edgeDifference - 2400) * alpha;
    });
    const penalized = gain - overlapCost * (1 - settings.overlap / 100) ** 2 * 450 - boundaryCost * (1 - settings.spill / 100) * .3;
    const repeated = 1 + (uses.get(entry.assetId) || 0) * settings.variety / 100 * .012;
    return { entry, gain, score: area > .3 ? penalized / Math.pow(area, .25) / repeated : -Infinity };
  }

  function choosePoint() {
    let winner = 0, highest = -1;
    for (let trial = 0; trial < 14; trial++) {
      const index = Math.floor(random() * width * height), p = index * 4;
      let error = 20;
      for (let c = 0; c < 3; c++) error += weights[c] * (canvas[p + c] - target[p + c]) ** 2;
      error /= 1 + coverage[index] * (1 - settings.overlap / 100) ** 2;
      error *= .65 + random() * .7;
      if (error > highest) { highest = error; winner = index; }
    }
    return { x: (winner % width + .5) / width, y: (Math.floor(winner / width) + .5) / height };
  }

  const gridColumns = clamp(Math.round(Math.sqrt(settings.count * width / height)), 1, settings.count);
  const gridRows = Math.max(1, Math.floor(settings.count / gridColumns));
  const total = settings.grid ? gridColumns * gridRows : settings.count;
  let deadline = performance.now() + 12, lastProgress = 0;
  for (let index = entries.length; index < total; index++) {
    if (cancelled()) throw new DOMException("Cancelled", "AbortError");
    const stage = index / Math.max(1, total - 1);
    const point = settings.grid ? { x: (index % gridColumns + .5) / gridColumns, y: (Math.floor(index / gridColumns) + .5) / gridRows } : choosePoint();
    const p = (clamp(Math.floor(point.y * height), 0, height - 1) * width + clamp(Math.floor(point.x * width), 0, width - 1)) * 4;
    const centerColor = [target[p], target[p + 1], target[p + 2]];
    const shortlist = assets.map(asset => {
      const color = asset.temporalMean || asset.mean;
      const distance = colorDistance(color, centerColor) * (1 - settings.recolor / 100 * .8);
      return { asset, distance: distance + (1 - asset.coverage) * 420 + (uses.get(asset.id) || 0) * settings.variety * .2 };
    }).sort((a, b) => a.distance - b.distance).slice(0, 28);
    const candidates = [];
    const attempts = settings.grid ? 12 : 10 + Math.round(fidelity * 6);
    for (let attempt = 0; attempt < attempts; attempt++) {
      const asset = shortlist[attempt === 0 ? 0 : Math.floor(random() ** 1.8 * shortlist.length)].asset;
      const size = settings.grid ? Math.min(width / gridColumns, height / gridRows) / shortSide :
        Math.max(1.8 / shortSide, settings.size / 100 * (1.7 - 1.2 * stage ** .65) * Math.exp((random() * 2 - 1) * settings.variation / 100 * 1.2));
      const jitter = settings.grid ? 0 : size * chaos * .65;
      const entry = { assetId: asset.id, x: clamp(point.x + (random() - .5) * jitter * shortSide / width, -.1, 1.1),
        y: clamp(point.y + (random() - .5) * jitter * shortSide / height, -.1, 1.1), size,
        rotation: settings.grid ? 0 : (random() * 2 - 1) * settings.rotation,
        opacity: 1 - random() * settings.transparency / 100,
        tintAmount: settings.recolor / 100 * (attempt % 4 === 0 ? .45 : 1), tint: [0, 0, 0], phase: asset.phase || 0 };
      candidates.push(evaluate(entry, centerColor));
    }
    candidates.sort((a, b) => b.score - a.score);
    const rank = initial.length || settings.grid ? 0 : random() < chaos * .4 ? Math.floor(random() * Math.min(3, candidates.length)) : 0;
    const chosen = candidates[rank];
    if (chosen && Number.isFinite(chosen.score) && (chosen.gain > 0 || settings.grid || (!initial.length && random() < chaos * .16))) apply(chosen.entry);
    if (performance.now() >= deadline) {
      if (performance.now() - lastProgress > 120) {
        progress({ fraction: (index + 1) / total, entries, pixels: new Uint8ClampedArray(canvas), width, height, background: bg });
        lastProgress = performance.now();
      }
      await yieldWork(); deadline = performance.now() + 12;
    }
  }
  const result = { entries, pixels: new Uint8ClampedArray(canvas), width, height, background: bg,
    settings, seed, baseError, initialError, error: imageError(canvas, pixels) };
  progress({ ...result, fraction: 1 });
  return result;
}
