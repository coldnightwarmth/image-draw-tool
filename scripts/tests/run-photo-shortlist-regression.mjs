#!/usr/bin/env node
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { performance } from 'node:perf_hooks';
import { createAssetShortlister, fitCollage, PRESETS } from '../../photo/matcher.mjs';

// The previous full-sort implementation is the behavioral reference, including
// its floating-point operation order and stable catalog-order tie breaking.
function referenceShortlister(assets, settings) {
  const weights = [.3, .5, .2];
  return (centerColor, uses) => assets.map(asset => {
    const color = asset.temporalMean || asset.mean;
    const distance = weights.reduce((sum, weight, channel) =>
      sum + weight * (color[channel] - centerColor[channel]) ** 2, 0) * (1 - settings.recolor / 100 * .8);
    return { asset, distance: distance + (1 - asset.coverage) * 420 +
      (uses.get(asset.id) || 0) * settings.variety * .2 };
  }).sort((a, b) => a.distance - b.distance).slice(0, 28).map(item => item.asset);
}

const matcherSource = await readFile(new URL('../../photo/matcher.mjs', import.meta.url), 'utf8');
const optimizedFactory = 'const selectAssets = createAssetShortlister(assets, settings);';
assert.equal(matcherSource.split(optimizedFactory).length, 2, 'replace exactly the production selection factory');
const baselineSource = matcherSource.replace(optimizedFactory, 'const selectAssets = referenceShortlister(assets, settings);') +
  '\n' + referenceShortlister.toString();
const baseline = await import('data:text/javascript;base64,' + Buffer.from(baselineSource).toString('base64'));
const manifest = JSON.parse(await readFile(new URL('../../photo/data/stock-index.json', import.meta.url), 'utf8'));
const assets = manifest.assets.map(asset => ({ ...asset, id: asset.source }));
const uses = new Map(assets.map((asset, index) => [asset.id, index % 11]));
const queries = Array.from({ length: 1000 }, (_, index) => [(index * 73) % 256, (index * 47) % 256, (index * 139) % 256]);
let rankingChecks = 0;
for (const settings of [PRESETS.loose, PRESETS.balanced, PRESETS.detailed, { recolor: 0, variety: 0 }, { recolor: 100, variety: 100 }]) {
  const actual = createAssetShortlister(assets, settings), expected = referenceShortlister(assets, settings);
  for (const color of queries) {
    assert.deepEqual(actual(color, uses).map(asset => asset.id), expected(color, uses).map(asset => asset.id));
    rankingChecks++;
  }
}

// Equal scores, fewer than 28 assets, and reuse changes must keep the same order.
for (const length of [0, 1, 27, 28, 29, 70]) {
  const tied = Array.from({ length }, (_, index) => ({ id: String(index), mean: [20, 30, 40], coverage: .75 }));
  const settings = { recolor: 35, variety: 70 }, counts = new Map();
  const actual = createAssetShortlister(tied, settings), expected = referenceShortlister(tied, settings);
  for (let pass = 0; pass < 40; pass++) {
    assert.deepEqual(actual([60, 70, 80], counts), expected([60, 70, 80], counts));
    counts.set(String(pass % Math.max(1, length)), pass);
    rankingChecks++;
  }
}

// Exercise the complete seeded fitter with stock metadata and small synthetic
// image tiles. This isolates fitter behavior without a browser/image decoder.
const tileSize = 8;
const fitAssets = assets.map((asset, index) => {
  const pixels = new Uint8ClampedArray(tileSize * tileSize * 4);
  for (let p = 0; p < tileSize * tileSize; p++) {
    const modulation = ((p + index) % 5 - 2) * 9;
    for (let channel = 0; channel < 3; channel++) pixels[p * 4 + channel] = asset.mean[channel] + modulation;
    pixels[p * 4 + 3] = (p * 17 % 64) / 64 < asset.coverage ? 255 : 0;
  }
  return { ...asset, pixels, tileSize };
});
const width = 224, height = 187, pixels = new Uint8ClampedArray(width * height * 4);
for (let y = 0; y < height; y++) for (let x = 0; x < width; x++) {
  pixels.set([x / width * 255, y / height * 255, (x * 11 + y * 7) % 256, 255], (y * width + x) * 4);
}
const hooks = { yieldWork: async () => {} };
const fitChecks = [];
for (const [label, settings, seed] of [
  ['loose', { ...PRESETS.loose, count: 200 }, 123],
  ['balanced', { ...PRESETS.balanced, count: 600 }, 0x1a2b3c4d],
  ['detailed', { ...PRESETS.detailed, count: 320 }, 0xffffffff],
  ['grid', { ...PRESETS.balanced, count: 200, grid: true }, 10]
]) {
  const input = { width, height, pixels, assets: fitAssets, settings, seed };
  const startReference = performance.now(), expected = await baseline.fitCollage(input, hooks);
  const referenceMs = performance.now() - startReference;
  const startActual = performance.now(), actual = await fitCollage(input, hooks);
  const optimizedMs = performance.now() - startActual;
  assert.deepEqual(actual, expected, `${label}: placements, pixels, errors and seed are exact`);
  const refinement = { ...input, settings: { ...settings, count: actual.entries.length + 80 },
    initial: actual.entries, background: actual.background };
  assert.deepEqual(await fitCollage(refinement, hooks), await baseline.fitCollage(refinement, hooks), `${label}: refinement is exact`);
  fitChecks.push({ label, placements: actual.entries.length, referenceMs, optimizedMs });
}

// Warm each implementation, alternate measurement order, and report medians.
// These are local microbenchmarks, not performance promises for a device/browser.
const settings = PRESETS.balanced;
const reference = referenceShortlister(assets, settings), optimized = createAssetShortlister(assets, settings);
let checksum = 0;
const measure = select => {
  const start = performance.now();
  for (const color of queries) checksum += select(color, uses)[0].coverage;
  return performance.now() - start;
};
measure(reference); measure(optimized);
const timings = { reference: [], optimized: [] };
for (let trial = 0; trial < 5; trial++) {
  for (const key of trial % 2 ? ['optimized', 'reference'] : ['reference', 'optimized']) {
    timings[key].push(measure(key === 'reference' ? reference : optimized));
  }
}
const median = values => values.toSorted((a, b) => a - b)[Math.floor(values.length / 2)];
assert(Number.isFinite(checksum));
console.log(JSON.stringify({ passed: true, assets: assets.length, rankingChecks, fitChecks,
  rankingBenchmark: { queries: queries.length, referenceMedianMs: median(timings.reference),
    optimizedMedianMs: median(timings.optimized), speedup: median(timings.reference) / median(timings.optimized) } }, null, 2));
