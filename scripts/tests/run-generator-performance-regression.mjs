#!/usr/bin/env node
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { resolve, extname, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = fileURLToPath(new URL('../../', import.meta.url));
const mime = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.css': 'text/css', '.gif': 'image/gif' };
const server = createServer(async (req, res) => {
  try {
    let pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
    if (pathname.endsWith('/')) pathname += 'index.html';
    const path = resolve(root, `.${pathname}`);
    if (!path.startsWith(resolve(root) + sep)) throw new Error('Invalid path');
    const data = await readFile(path);
    res.writeHead(200, { 'Content-Type': mime[extname(path)] || 'application/octet-stream' });
    res.end(data);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const url = `http://127.0.0.1:${server.address().port}/generator/?seed=deadbeef`;
const browser = await chromium.launch({ headless: true });
const results = [];
try {
  for (const profile of [
    { name: 'desktop', viewport: { width: 1440, height: 900 }, deviceScaleFactor: 1, hasTouch: false, rate: 1 },
    { name: 'surface-emulation', viewport: { width: 1368, height: 912 }, deviceScaleFactor: 2, hasTouch: true, rate: 4 },
    { name: 'phone-emulation', viewport: { width: 390, height: 844 }, deviceScaleFactor: 3, hasTouch: true, rate: 4 }
  ]) {
    const context = await browser.newContext({ viewport: profile.viewport, deviceScaleFactor: profile.deviceScaleFactor, hasTouch: profile.hasTouch });
    const page = await context.newPage();
    page.setDefaultTimeout(60000);
    const errors = [];
    page.on('pageerror', error => errors.push(error.message));
    const cdp = await context.newCDPSession(page);
    await cdp.send('Emulation.setCPUThrottlingRate', { rate: profile.rate });
    await cdp.send('Performance.enable');
    if (process.env.GENERATOR_UNBATCHED_BASELINE === '1') {
      // Diagnostic control: restore only the old per-stamp read/write order.
      await page.route('**/generator.js?*', async route => {
        const response = await route.fetch();
        let source = await response.text();
        source = source.replace('const presentations = images.map((image) => {', 'const readPresentation = (image) => {');
        source = source.replace('    });\n    let hasPendingPreview = false;', '    };\n    let hasPendingPreview = false;');
        source = source.replace('images[index], presentations[index]', 'images[index], readPresentation(images[index])');
        await route.fulfill({ response, body: source });
      });
    }
    await page.goto(url, { waitUntil: 'load' });
    await page.waitForFunction(() => window.GeneratorApp?.getSummary().count === 120 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
    // Worst-case live pixelation: all 120 stamps need a canvas proxy.
    await page.evaluate(async () => {
      document.querySelector('#generatorSequenceEnabledToggle').checked = true;
      for (const input of document.querySelectorAll('.generator-sequence-effect-checkbox')) input.checked = input.value === 'pixelate';
      for (const input of document.querySelectorAll('.generator-sequence-timing-checkbox')) input.checked = input.value === 'all';
      await window.GeneratorApp.generate(0x12345678);
    });
    await page.waitForFunction(() => document.querySelector('.generator-pixelate-proxy:not([hidden])'));
    const before = (await cdp.send('Performance.getMetrics')).metrics;
    const frameGaps = await page.evaluate(() => new Promise(resolve => {
      const gaps = []; let previous = performance.now(); const start = previous;
      function tick(now) { gaps.push(now - previous); previous = now; if (now - start < 1500) requestAnimationFrame(tick); else resolve(gaps); }
      requestAnimationFrame(tick);
    }));
    const after = (await cdp.send('Performance.getMetrics')).metrics;
    const delta = name => after.find(m => m.name === name).value - before.find(m => m.name === name).value;
    if (profile.name === 'desktop') {
      await page.locator('#generatorBookmarkButton').click({ force: true });
      await page.waitForFunction(() => document.querySelector('.generator-bookmark-preview'));
      const retained = await page.evaluate(async () => {
        const image = document.querySelector('.generator-bookmark-preview');
        const src = image.src;
        await window.GeneratorApp.randomizeBackground();
        return image.isConnected && image === document.querySelector('.generator-bookmark-preview') && image.src === src;
      });
      assert.equal(retained, true, 'control edits must retain decoded bookmark thumbnails');
    }
    // Foreign fingers/pens must not move or end the active gesture; lost capture
    // must remove listeners so subsequent moves cannot change the range.
    const pointer = await page.evaluate(() => {
      const handle = document.querySelector('#generatorSizeRandomMinSlider');
      handle.value = '100';
      document.querySelector('#generatorSizeRandomMaxSlider').value = '900';
      const wrapper = handle.parentElement;
      const rect = wrapper.getBoundingClientRect();
      const capture = wrapper.setPointerCapture;
      wrapper.setPointerCapture = () => {}; // Synthetic events cannot establish native capture.
      const send = (type, id, x) => wrapper.dispatchEvent(new PointerEvent(type, { pointerId: id, pointerType: 'touch', isPrimary: true, button: 0, clientX: x, bubbles: true }));
      send('pointerdown', 1, rect.left + rect.width * 0.2);
      const start = handle.value;
      send('pointermove', 2, rect.right);
      const foreign = handle.value;
      send('pointerup', 2, rect.right);
      send('pointermove', 1, rect.left + rect.width * 0.3);
      const moved = handle.value;
      send('lostpointercapture', 1, rect.left);
      send('pointermove', 1, rect.right);
      const ended = handle.value;
      wrapper.setPointerCapture = capture;
      return { start, foreign, moved, ended, width: rect.width };
    });
    assert.equal(pointer.start, pointer.foreign);
    assert.ok(pointer.width > 0);
    assert.notEqual(pointer.start, pointer.moved);
    assert.equal(pointer.moved, pointer.ended);
    await page.setViewportSize({ width: profile.viewport.height, height: profile.viewport.width });
    await page.waitForTimeout(300);
    const bounds = await page.locator('#generatorCanvas').boundingBox();
    assert.ok(bounds.width > 0 && bounds.height > 0);
    assert.deepEqual(errors, []);
    frameGaps.sort((a,b) => a-b);
    results.push({ profile: profile.name, frames: frameGaps.length, p95FrameGapMs: Math.round(frameGaps[Math.floor(frameGaps.length * .95)]), styleRecalculations: delta('RecalcStyleCount'), styleTimeMs: Math.round(delta('RecalcStyleDuration') * 1000), layoutCount: delta('LayoutCount') });
    await context.close();
  }
  const context = await browser.newContext();
  const page = await context.newPage();
  await page.goto(url, { waitUntil: 'load' });
  const pixelParity = await page.evaluate(async () => {
    const worker = new Worker('../export-raster-worker.js', { type: 'module' });
    let id = 0;
    const pending = new Map();
    worker.onmessage = ({ data }) => {
      if (data.type === 'progress') return;
      const request = pending.get(data.requestId);
      if (!request) return;
      pending.delete(data.requestId);
      clearTimeout(request.timer);
      if (data.type === 'error') request.reject(new Error(data.error.message));
      else request.resolve(data);
    };
    const request = (type, values = {}) => new Promise((resolve, reject) => {
      const requestId = String(++id);
      const timer = setTimeout(() => reject(new Error('Worker test timed out')), 30000);
      pending.set(requestId, { resolve, reject, timer });
      worker.postMessage({ protocol: 'brush-export-raster', version: 1, jobId: 'parity', requestId, type, ...values });
    });
    try {
      const canvas = new OffscreenCanvas(20, 20);
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = 'rgba(240, 81, 26, 0.6)'; ctx.fillRect(0, 0, 20, 20);
      const blob = await canvas.convertToBlob({ type: 'image/png' });
      const width = 1200, height = 800;
      const regular = [{ sourceId: 'test', width: 550, height: 400, centerX: 600, centerY: 400, opacity: 0.63 }];
      const overlay = [{ sourceId: 'test', width: 250, height: 350, centerX: 120, centerY: 90, opacity: 0.37 }];
      await request('prepare', { scene: {
        outputWidth: width, outputHeight: height, entries: [...regular, ...overlay],
        background: { include: false, matteColor: '' },
        assets: [{ id: 'test', kind: 'static', blob }]
      } });
      const render = async (entries, extra = {}) => (await request('render-frame', { output: 'rgba', entries, ...extra })).output;
      const regularPixels = new Uint8ClampedArray((await render(regular)).buffer);
      const overlayPixels = new Uint8ClampedArray((await render(overlay)).buffer);
      const background = [18, 52, 86];
      let compared = 0;
      for (const margin of [0, 144]) {
        for (const regularEntries of [regular, []]) {
          const expected = regularEntries.length ? regularPixels.slice() : new Uint8ClampedArray(width * height * 4);
          for (let offset = 0; offset < expected.length; offset += 4) {
            const alpha = expected[offset + 3] / 255;
            const x = (offset / 4) % width, y = Math.floor(offset / 4 / width);
            const cropped = x < margin || x >= width - margin || y < margin || y >= height - margin;
            for (let channel = 0; channel < 3; channel++) {
              expected[offset + channel] = cropped ? background[channel] : Math.round(expected[offset + channel] * alpha + background[channel] * (1 - alpha));
              const overAlpha = overlayPixels[offset + 3] / 255;
              expected[offset + channel] = Math.round(overlayPixels[offset + channel] * overAlpha + expected[offset + channel] * (1 - overAlpha));
            }
            expected[offset + 3] = 255;
          }
          const composite = { background: '#123456', crop: { margin, width, height }, overlayEntries: overlay };
          const actual = new Uint8ClampedArray((await render(regularEntries, { generatorComposite: composite })).buffer);
          for (let i = 0; i < expected.length; i++) if (expected[i] !== actual[i]) throw new Error(`RGBA mismatch at ${i}`);
          const webp = await render(regularEntries, { output: 'webp', generatorComposite: composite });
          const bitmap = await createImageBitmap(webp.blob);
          const output = new OffscreenCanvas(width, height).getContext('2d');
          output.drawImage(bitmap, 0, 0); bitmap.close();
          const decoded = output.getImageData(0, 0, width, height).data;
          for (let i = 0; i < expected.length; i++) if (expected[i] !== decoded[i]) throw new Error(`WebP mismatch at ${i}`);
          compared += expected.length;
        }
      }
      // Direct WebP fast path: no crop or overlays, opaque background.
      const backgroundOverride = { include: true, color: '#123456', matteColor: '#123456' };
      const raw = new Uint8ClampedArray((await render(regular, { background: backgroundOverride })).buffer);
      const fast = await render(regular, { output: 'webp', background: backgroundOverride });
      const bitmap = await createImageBitmap(fast.blob);
      const output = new OffscreenCanvas(width, height).getContext('2d');
      output.drawImage(bitmap, 0, 0); bitmap.close();
      const decoded = output.getImageData(0, 0, width, height).data;
      for (let i = 0; i < raw.length; i++) if (raw[i] !== decoded[i]) throw new Error(`Fast WebP mismatch at ${i}`);
      return { comparedRgbaBytes: compared + raw.length, width, height };
    } finally {
      worker.terminate();
      for (const request of pending.values()) clearTimeout(request.timer);
    }
  });
  await context.close();
  console.log(JSON.stringify({ results, pixelParity }, null, 2));
  console.log('Generator device/performance regression passed; emulation is not physical-device validation.');
} finally { await browser.close(); await new Promise(resolve => server.close(resolve)); }
