#!/usr/bin/env node
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { extname, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = fileURLToPath(new URL('../../', import.meta.url));
const workerSource = await readFile(resolve(root, 'export-raster-worker.js'), 'utf8');
// A test-only baseline bypasses optional effects reuse and draw culling. An
// actual pre-change worker may also be supplied for independent comparisons.
const baselineSource = process.env.RASTER_BASELINE
  ? await readFile(process.env.RASTER_BASELINE, 'utf8')
  : workerSource
    .replace('function isEntryOutsideOutput(scene, entry, scaleX, scaleY) {',
      'function isEntryOutsideOutput(scene, entry, scaleX, scaleY) { return false;')
    .replace('function getEffectRasterKey(job, asset, frameIndex, entry, drawWidth, drawHeight) {',
      'function getEffectRasterKey(job, asset, frameIndex, entry, drawWidth, drawHeight) { return null;')
    .replace(/function resolveAssetFrameIndex[\s\S]*?\n}\n/, `function resolveAssetFrameIndex(asset, timeMs, phaseOffsetMs = 0, playbackRate = 1) {
      if (!asset || !asset.frames.length) return -1;
      if (asset.frames.length === 1 || asset.totalDurationMs <= 0 || playbackRate <= 0) return 0;
      const duration = Math.max(1, asset.totalDurationMs);
      let wrapped = (finiteNumber(timeMs, 0) * playbackRate + phaseOffsetMs) % duration;
      if (wrapped < 0) wrapped += duration;
      let elapsed = 0;
      for (let index = 0; index < asset.frames.length; index++) {
        elapsed += Math.max(MIN_GIF_FRAME_DELAY_MS, finiteNumber(asset.frames[index].durationMs, DEFAULT_GIF_FRAME_DELAY_MS));
        if (wrapped < elapsed) return index;
      }
      return asset.frames.length - 1;
    }\n`);
const instrument = source => source.replace('async function dispatchMessage(message) {', `
async function dispatchMessage(message) {
  if (message.type === "test-pressure") {
    const job = jobs.get(message.jobId);
    const before = job.effectRasterBytes;
    const bytes = job.memoryBudgetBytes - job.decodedBitmapBytes -
      Math.max(job.canvasBytes, job.outputWorkingSetReserveBytes) + before;
    reserveDecodedBitmapBytes(job, bytes, { phase: "test-essential-allocation" });
    const after = job.effectRasterBytes;
    releaseDecodedBitmapBytes(job, bytes);
    post("test-pressure", { requestId: message.requestId, before, after });
    return;
  }
  if (message.type === "test-stats") {
    const job = jobs.get(message.jobId);
    post("test-stats", { requestId: message.requestId, stats: job ? {
      effects: job.effectRasters?.size || 0,
      effectBytes: job.effectRasterBytes || 0,
      demand: job.effectRasterDemand?.size || 0,
      styles: job.effectRasterStyles?.size || 0,
      budget: job.memoryBudgetBytes,
      used: getProjectedJobMemoryBytes(job),
      decodedFrames: job.qualityDecoder?.stats.decodedFrames || 0
    } : null });
    return;
  }
`);
const mime = { '.js': 'text/javascript', '.mjs': 'text/javascript', '.html': 'text/html', '.gif': 'image/gif', '.wasm': 'application/wasm' };
const server = createServer(async (request, response) => {
  try {
    const pathname = new URL(request.url, 'http://localhost').pathname;
    if (pathname === '/') {
      response.writeHead(200, { 'Content-Type': 'text/html' });
      response.end('<!doctype html><title>Raster regression</title>');
      return;
    }
    const path = resolve(root, `.${decodeURIComponent(pathname)}`);
    if (!path.startsWith(resolve(root) + sep)) throw Error('Invalid path');
    const data = pathname === '/optimized-worker.js' ? instrument(workerSource)
      : pathname === '/baseline-worker.js' ? instrument(baselineSource) : await readFile(path);
    response.writeHead(200, { 'Content-Type': mime[extname(path)] || 'application/octet-stream' });
    response.end(data);
  } catch { response.writeHead(404); response.end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
let browser;
try {
  browser = await chromium.launch({ headless: true,
    ...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH ? { executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH } : {}) });
  const page = await browser.newPage();
  page.setDefaultTimeout(120000);
  const errors = [];
  page.on('pageerror', error => errors.push(error.message));
  await page.goto(`http://127.0.0.1:${server.address().port}/`);
  await page.addScriptTag({ url: '/gif.js' });
  const result = await page.evaluate(async runBenchmark => {
    const check = (condition, message) => { if (!condition) throw Error(message); };
    const fixture = new OffscreenCanvas(96, 72), fixtureContext = fixture.getContext('2d');
    const pixels = fixtureContext.createImageData(96, 72);
    for (let i = 0; i < pixels.data.length; i += 4) {
      pixels.data[i] = (i / 4 * 17) % 256;
      pixels.data[i + 1] = (i / 4 * 31) % 256;
      pixels.data[i + 2] = (i / 4 * 53) % 256;
      pixels.data[i + 3] = [0, 53, 127, 255][(i / 4) % 4];
    }
    fixtureContext.putImageData(pixels, 0, 0);
    const png = await fixture.convertToBlob({ type: 'image/png' });
    const gif = new GIF({ workers: 1, workerScript: '/gif.worker.js', width: 96, height: 72, quality: 1, dither: false, repeat: 0 });
    for (const [frame, delay] of [20, 40, 80, 30, 60, 110, 20].entries()) {
      const image = new ImageData(new Uint8ClampedArray(pixels.data), 96, 72);
      for (let i = 0; i < image.data.length; i += 4) {
        image.data[i] = (image.data[i] + frame * 31) % 256;
        image.data[i + 3] = 255;
      }
      gif.addFrame(image, { delay });
    }
    const gifBlob = await new Promise((resolve, reject) => {
      gif.on('finished', resolve); gif.on('abort', reject); gif.render();
    });
    function session(path) {
      const worker = new Worker(path, { type: 'module' }), pending = new Map();
      let id = 0;
      worker.onmessage = ({ data }) => {
        if (data.type === 'progress' || !pending.has(data.requestId)) return;
        const request = pending.get(data.requestId); pending.delete(data.requestId); clearTimeout(request.timer);
        if (data.type === 'error') request.reject(Error(data.error.message)); else request.resolve(data);
      };
      worker.onerror = event => { for (const request of pending.values()) request.reject(Error(event.message)); };
      return {
        request(type, values = {}) {
          return new Promise((resolve, reject) => {
            const requestId = String(++id), timer = setTimeout(() => reject(Error(`Worker timeout: ${type}`)), 60000);
            pending.set(requestId, { resolve, reject, timer });
            worker.postMessage({ protocol: 'brush-export-raster', version: 1, jobId: 'fixture', requestId, type, ...values });
          });
        }, close() { worker.terminate(); }
      };
    }
    const baseline = session('/baseline-worker.js'), optimized = session('/optimized-worker.js');
    const baseEntry = { sourceId: 'gif', centerX: 70, centerY: 60, width: 132, height: 99,
      opacity: .83, imageRendering: 'auto', colorFilter: 'sepia(0.4) saturate(3) hue-rotate(120deg)', pixelateAmount: 4 };
    const colorMatrix = [.8, .1, 0, 0, .04, 0, .9, .1, 0, 0, .1, 0, .9, 0, 0, 0, 0, 0, 1, 0];
    const entries = Array.from({ length: 120 }, (_, i) => ({ ...baseEntry,
      sourceId: i % 3 ? 'gif' : 'png', centerX: -90 + (i % 12) * 43, centerY: -60 + Math.floor(i / 12) * 38,
      width: 51.3 + (i % 7) * 8, height: 39.4 + (i % 5) * 8,
      rotation: i * 27.3, opacity: i % 9 ? .53 + (i % 3) * .17 : 0,
      transformMatrix: i % 4 ? null : [.7, -.4, .27, 1.2],
      phaseOffsetMs: i % 7 * 39 - 230, playbackRate: i % 11 ? .73 : 0,
      colorFilter: i % 4 ? baseEntry.colorFilter : 'contrast(2.3) saturate(.4) hue-rotate(73deg)',
      tintLayers: i % 6 ? [] : [{ color: '#ef4578', amountPercent: 17 }],
      colorMatrix: i % 8 ? null : colorMatrix, pixelateAmount: i % 3 ? 4 : 0,
      blurAmount: i % 10 ? 0 : 3.2,
      blendMode: ['normal', 'multiply', 'screen', 'difference'][i % 4]
    }));
    // Outside source bounds but visible blur; culling must retain this halo.
    entries.push({ ...baseEntry, sourceId: 'png', centerX: -12, centerY: 135, width: 16, height: 100, blurAmount: 14 });
    const scene = (items, quality = false, width = 360, height = 240) => ({ quality,
      outputWidth: width, outputHeight: height,
      selectionBounds: { left: 0, top: 0, right: width, bottom: height }, entries: items,
      background: { include: false, matteColor: '' }, memoryBudgetBytes: 32 * 1024 * 1024,
      assets: [{ id: 'gif', kind: 'gif', blob: gifBlob, frameIntervalMs: 20 }, { id: 'png', kind: 'static', blob: png }]
    });
    const hashes = [], stats = [];
    let pixelsCompared = 0;
    async function compare(frame, label) {
      const left = (await baseline.request('render-frame', { output: 'rgba', ...frame })).output;
      const right = (await optimized.request('render-frame', { output: 'rgba', ...frame })).output;
      const a = new Uint8Array(left.buffer), b = new Uint8Array(right.buffer);
      check(a.length === b.length, `${label}: size mismatch`);
      for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) throw Error(`${label}: pixel byte ${i}: ${a[i]} != ${b[i]}`);
      pixelsCompared += a.length / 4;
      return Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', b)), n => n.toString(16).padStart(2, '0')).join('');
    }
    try {
      for (const quality of [false, true]) {
        await baseline.request('prepare', { scene: scene(entries, quality) });
        await optimized.request('prepare', { scene: scene(entries, quality) });
        for (const timeMs of [0, 0, 0, 20, 39, 40, 179, 340, 500, -45, 0]) {
          hashes.push(await compare({ entries: entries.map(entry => ({ ...entry })), timeMs }, `quality=${quality} time=${timeMs}`));
        }
        // Changing filters, dimensions, phase and opacity must not reuse stale pixels.
        const edited = entries.map((entry, i) => ({ ...entry, colorFilter: i % 2 ? 'hue-rotate(213deg)' : entry.colorFilter,
          width: entry.width * 1.21, height: entry.height * .87, phaseOffsetMs: entry.phaseOffsetMs + 121, opacity: .4 }));
        for (let repeat = 0; repeat < 3; repeat++) {
          await compare({ entries: edited, timeMs: 50, generatorComposite: {
            background: '#4e2731', crop: { margin: 19, opacity: .37, width: 360, height: 240 },
            overlayEntries: edited.slice(0, 18)
          } }, `crop and edits ${quality}/${repeat}`);
        }
        const current = (await optimized.request('test-stats')).stats;
        check(current.effects > 0, 'Repeated filtered frames should populate their exact cache');
        check(current.effectBytes <= current.budget / 16, 'Effect cache exceeded its memory cap');
        check(current.used <= current.budget, 'Worker exceeded its memory budget');
        check(current.demand <= 2048, 'Effect demand metadata must stay bounded');
        check(current.styles <= 2048, 'Per-entry cache admission metadata must stay bounded');
        stats.push(current);
        const pressure = await optimized.request('test-pressure');
        check(pressure.before > 0 && pressure.after === 0, 'Essential allocations must evict optional effect rasters first');
        await compare({ entries: edited, timeMs: 50 }, `after essential-allocation cache eviction ${quality}`);
        const stretchedScene = scene(entries, quality);
        stretchedScene.selectionBounds = { left: -50, top: -30, right: 430, bottom: 120 };
        await baseline.request('prepare', { scene: stretchedScene });
        await optimized.request('prepare', { scene: stretchedScene });
        await compare({ timeMs: 80 }, `anisotropic output scale ${quality}`);
      }
      // A fully invisible quality frame should never decompress its GIF.
      const invisible = Array.from({ length: 300 }, (_, i) => ({ ...baseEntry, centerX: i % 2 ? -1000 : 100,
        opacity: i % 2 ? 1 : 0, phaseOffsetMs: i * 11 }));
      await baseline.request('prepare', { scene: scene(invisible, true) });
      await optimized.request('prepare', { scene: scene(invisible, true) });
      await compare({ timeMs: 80 }, 'invisible source decode');
      check((await optimized.request('test-stats')).stats.decodedFrames === 0, 'Invisible stamps decoded GIF frames');

      const timings = [];
      for (const scenario of (runBenchmark ? ['repeated-effects', 'offscreen-effects', 'unique-static-effects', 'changing-effects'] : [])) {
        const items = Array.from({ length: 300 }, (_, i) => ({ ...baseEntry,
          centerX: scenario === 'offscreen-effects' && i % 4 ? -500 : 20 + i % 20 * 30,
          centerY: 20 + Math.floor(i / 20) * 23, width: 132, height: 99,
          sourceId: i % 2 ? 'gif' : 'png', phaseOffsetMs: i % 3 * 70,
          colorFilter: ['changing-effects', 'unique-static-effects'].includes(scenario) ? `sepia(.4) saturate(3) hue-rotate(${i}deg)` : baseEntry.colorFilter
        }));
        for (const quality of [false, true]) {
          await baseline.request('prepare', { scene: scene(items, quality, 640, 360) });
          await optimized.request('prepare', { scene: scene(items, quality, 640, 360) });
          const rounds = { baseline: [], optimized: [] };
          for (let round = 0; round < 3; round++) {
            for (const [name, renderer] of (round % 2 ? [['optimized', optimized], ['baseline', baseline]] : [['baseline', baseline], ['optimized', optimized]])) {
              const started = performance.now();
              for (let frame = 0; frame < 9; frame++) {
                await renderer.request('render-frame', { output: 'rgba', timeMs: frame * 1000 / 60,
                  entries: items.map((entry, i) => ({ ...entry, rotation: frame * 2 + i % 10,
                    ...(scenario === 'changing-effects' ? { colorFilter: `hue-rotate(${frame * 20 + round * 200 + i}deg)` } : {}) })) });
              }
              rounds[name].push(performance.now() - started);
            }
          }
          const median = values => values.slice().sort((a, b) => a - b)[1];
          timings.push({ scenario, quality, baselineMs: Math.round(median(rounds.baseline)),
            optimizedMs: Math.round(median(rounds.optimized)), speedup: +(median(rounds.baseline) / median(rounds.optimized)).toFixed(2) });
        }
      }
      await optimized.request('release');
      check((await optimized.request('test-stats')).stats === null, 'Released job retained its caches');
      return { pixelsCompared, distinctFrameHashes: new Set(hashes).size, stats, timings };
    } finally { baseline.close(); optimized.close(); }
  }, process.env.RASTER_SKIP_BENCHMARK !== '1');
  assert.deepEqual(errors, []);
  assert.ok(result.distinctFrameHashes > 2, 'The parity fixtures must actually animate');
  console.log('PASS exact raster reuse, clipping and animation parity', JSON.stringify(result, null, 2));
} finally {
  await browser?.close();
  await new Promise(resolve => server.close(resolve));
}
