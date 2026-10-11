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
const context = await browser.newContext({ viewport: { width: 1368, height: 912 }, deviceScaleFactor: 2, hasTouch: true });
const page = await context.newPage();
page.setDefaultTimeout(120000);
const errors = [];
page.on('pageerror', error => errors.push(error.message));
const configureDenseFixture = async () => {
  // Future-composition randomization is a product default, not part of this
  // controlled 300-stamp stability fixture.
  for (const toggle of document.querySelectorAll('#generatorControlsMain input[type="checkbox"][id$="RandomToggle"]')) toggle.checked = false;
  const categories = ['radial', 'flower', 'garden', 'stroke', 'esp ra de glitch', 'esp ra de', 'esp ra de characters', 'particles', '3d', 'pixel art+games', 'anime', 'misc', 'framing', 'nu'];
  for (const input of document.querySelectorAll('.generator-source-checkbox[data-source-kind="category"]')) input.checked = categories.includes(input.value);
  document.querySelector('#generatorCategoryTab').click();
  const values = {
    generatorCanvasWidthInput: 1200, generatorCanvasHeightInput: 800,
    generatorCountSlider: 300, generatorMarkCountSlider: 12, generatorGifsPerMarkSlider: 100,
    generatorMarginSlider: 0, generatorMarginOpacitySlider: 100, generatorCropExemptionSlider: 0,
    generatorSizeSlider: 92, generatorSizeRandomMinSlider: 46, generatorSizeRandomMaxSlider: 158,
    generatorSpacingSlider: 54, generatorRotationSlider: 0, generatorOpacitySlider: 100,
    generatorTintAmountSlider: 0, generatorPitchSlider: 0, generatorYawSlider: 0,
    generatorHorizontalStretchSlider: 100, generatorVerticalStretchSlider: 100,
    generatorSpraySpreadSlider: 230, generatorLineAngleSlider: 0, generatorLineLengthSlider: 460,
    generatorLineCurveAmountSlider: 0, generatorLineCurveStrengthSlider: 0,
    generatorBoxWidthSlider: 380, generatorBoxHeightSlider: 260, generatorBoxStyleSelect: 'outline',
    generatorSequenceSpeedMinSlider: 52, generatorSequenceSpeedSlider: 78,
    generatorSequenceIntensityMinSlider: 47, generatorSequenceIntensitySlider: 78,
    generatorSequenceNoneFrequencySlider: 0, generatorBackgroundColorInput: '#ffffff', generatorTintColorInput: '#ff4fb3'
  };
  for (const [id, value] of Object.entries(values)) {
    const input = document.getElementById(id);
    if (!input) throw Error(`Missing controlled fixture input: ${id}`);
    input.value = String(value);
  }
  document.querySelector('input[name="generatorMarginMode"][value="placement"]').checked = true;
  document.querySelector('#generatorGifRandomToggle').checked = true;
  document.querySelector('#generatorSizeRandomToggle').checked = true;
  document.querySelector('#generatorSmoothPreviewToggle').checked = false;
  document.querySelector('#generatorSequenceEnabledToggle').checked = true;
  for (const input of document.querySelectorAll('.generator-mode-checkbox')) input.checked = ['scatter', 'spray', 'line', 'box', 'ellipse'].includes(input.value);
  for (const input of document.querySelectorAll('.generator-sequence-effect-checkbox')) input.checked = ['show-hide', 'move', 'rotate', 'scale', 'color-cycle', 'image-cycle', 'pixelate', 'blur'].includes(input.value);
  for (const input of document.querySelectorAll('.generator-sequence-timing-checkbox')) input.checked = ['pulse', 'wave', 'step', 'random', 'all', 'grouped'].includes(input.value);
  if (!await window.GeneratorApp.generate(0x12345678)) throw Error('Could not generate the controlled dense fixture');
};
await page.addInitScript(() => {
  const NativeWorker = window.Worker;
  window.__rasterRequests = [];
  window.__pendingRasterFrames = 0;
  window.__maxPendingRasterFrames = 0;
  window.Worker = class extends NativeWorker {
    constructor(...args) {
      super(...args);
      this.frames = new Set();
      this.addEventListener('message', ({ data }) => {
        if ((data.type === 'rendered' || data.type === 'error') && this.frames.delete(data.requestId)) window.__pendingRasterFrames--;
      });
    }
    postMessage(message, ...args) {
      if (window.__failPreviewOnce && message.type === 'render-frame' && message.output === 'bitmap') {
        window.__failPreviewOnce = false;
        queueMicrotask(() => this.dispatchEvent(new MessageEvent('message', { data: { protocol: 'brush-export-raster', version: 1, type: 'error', requestId: message.requestId, error: { message: 'Simulated preview failure' } } })));
        return;
      }
      if (message.type === 'render-frame') {
        this.frames.add(message.requestId);
        window.__pendingRasterFrames++;
        window.__maxPendingRasterFrames = Math.max(window.__maxPendingRasterFrames, window.__pendingRasterFrames);
        window.__rasterRequests.push({ output: message.output, count: message.entries.length, overlayCount: message.generatorComposite?.overlayEntries?.length || 0, entries: message.entries.map(e => e.sourceId) });
        if (window.__rasterRequests.length > 1000) window.__rasterRequests.shift();
      }
      return super.postMessage(message, ...args);
    }
    terminate() { window.__pendingRasterFrames -= this.frames.size; this.frames.clear(); return super.terminate(); }
  };
});
try {
  let delayInitialGifs = true;
  await page.route('**/*.gif?*', async route => {
    if (delayInitialGifs) await new Promise(resolve => setTimeout(resolve, 1000));
    await route.continue();
  });
  await page.goto(url, { waitUntil: 'domcontentloaded' });
  assert.equal(await page.locator('#generatorLoadingSpinner').isVisible(), true);
  delayInitialGifs = false;
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count > 0 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
  await page.waitForFunction(() => document.querySelector('#generatorLoadingSpinner').hidden);
  await page.unroute('**/*.gif?*');
  assert.equal(await page.locator('#generatorSmoothPreviewToggle').isChecked(), false);
  assert.equal(await page.locator('#generatorControlsMain > .generator-preview-option').getByText('smooth render preview', { exact: true }).count(), 1);
  assert.equal(await page.locator('#generatorSmoothPreviewToggle').evaluate(input => input.closest('.generator-preview-option') === document.querySelector('#generatorControlsMain').lastElementChild), true, 'smooth preview should remain below all sidebar categories');
  await page.evaluate(configureDenseFixture);
  assert.equal(await page.evaluate(() => window.GeneratorApp.getSummary().count), 300);
  assert.equal(await page.evaluate(() => GeneratorApp.getSummary().previewRenderer), 'dom');
  await page.locator('#generatorSmoothPreviewToggle').check({ force: true });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 5, null, { timeout: 120000 });
  const dense = await page.evaluate(() => ({
    summary: window.GeneratorApp.getSummary(),
    display: getComputedStyle(document.querySelector('#generatorComposition')).display,
    frames: window.__rasterRequests.filter(r => r.output === 'bitmap').map(r => r.count + r.overlayCount),
    maxPending: window.__maxPendingRasterFrames
  }));
  assert.equal(dense.summary.count, 300);
  assert.equal(dense.summary.previewRenderer, 'worker');
  assert.equal(dense.display, 'none');
  assert.ok(dense.frames.length >= 5);
  assert.ok(dense.frames.every(count => count === 300));
  assert.equal(dense.maxPending, 1, 'preview should have only one outstanding frame');
  await page.screenshot({ path: '/tmp/generator-300-stable.png' });
  const firstSidebar = await page.locator('.generator-panel-header').screenshot();
  await page.waitForTimeout(500);
  const secondSidebar = await page.locator('.generator-panel-header').screenshot();
  assert.deepEqual(firstSidebar, secondSidebar, 'sidebar should not repaint with artwork frames');
  console.log('300-stamp complete-frame preview and sidebar checks passed');
  // Editing the background must preserve complete-frame rendering.
  await page.evaluate(() => window.GeneratorApp.randomizeBackground());
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 3);
  // Enable crop inspection on the dense scene, then restore the flattened preview.
  await page.evaluate(async () => {
    document.querySelector('#generatorMarginSlider').value = '100';
    document.querySelector('input[name="generatorMarginMode"][value="crop"]').checked = true;
    await window.GeneratorApp.generate(0x12345678);
  });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 3);
  await page.locator('#generatorCropInspectButton').click({ force: true });
  assert.equal(await page.locator('#generatorStablePreview').isVisible(), false);
  await page.locator('#generatorCropInspectButton').click({ force: true });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 3);
  console.log('Crop inspection resume passed');
  // Paused sequences still render GIF frames; restoring context restarts safely.
  await page.locator('#generatorSequencePauseButton').click({ force: true });
  const pausedAt = await page.evaluate(() => window.GeneratorApp.getSummary().previewFrames);
  await page.waitForFunction(previous => window.GeneratorApp.getSummary().previewFrames > previous + 2, pausedAt);
  await page.evaluate(() => {
    const canvas = document.querySelector('#generatorStablePreview');
    canvas.dispatchEvent(new Event('contextlost', { cancelable: true }));
    canvas.dispatchEvent(new Event('contextrestored'));
  });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 3);
  await page.locator('#generatorSequencePauseButton').click({ force: true });
  console.log('Pause and context restoration passed');
  // A failed frame restores the DOM and retires the worker, rather than hanging.
  await page.evaluate(() => { window.__failPreviewOnce = true; });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewRenderer === 'dom-fallback');
  assert.notEqual(await page.locator('#generatorComposition').evaluate(el => getComputedStyle(el).display), 'none');
  await page.evaluate(() => window.GeneratorApp.generate(0xfeedbeef));
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 3);
  console.log('Renderer failure recovery passed');
  // Native mode must bypass the raster worker and retain all native stamps.
  const nativeSignature = await page.evaluate(() => window.GeneratorApp.getSummary().signature);
  await page.locator('#generatorSmoothPreviewToggle').uncheck({ force: true });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewRenderer === 'dom');
  const nativeFrames = await page.evaluate(() => window.__rasterRequests.filter(r => r.output === 'bitmap').length);
  await page.waitForTimeout(500);
  assert.equal(await page.evaluate(() => window.__rasterRequests.filter(r => r.output === 'bitmap').length), nativeFrames);
  assert.equal(await page.locator('#generatorComposition img.generator-stamp').count(), 300);
  assert.notEqual(await page.locator('#generatorComposition').evaluate(el => getComputedStyle(el).display), 'none');
  assert.equal(await page.evaluate(() => window.GeneratorApp.getSummary().signature), nativeSignature);
  await page.locator('#generatorSmoothPreviewToggle').check({ force: true });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewFrames >= 5);
  await page.waitForFunction(() => !document.querySelector('#generatorLowFps').hidden);
  assert.equal(await page.locator('#generatorLoadingSpinner').isVisible(), false);
  const header = await page.locator('.generator-canvas-header').boundingBox();
  const seedLabel = await page.locator('#generatorCanvasSeed').boundingBox();
  const indicator = await page.locator('#generatorLowFps').boundingBox();
  assert.ok(indicator.x >= seedLabel.x + seedLabel.width);
  assert.ok(indicator.y >= header.y && indicator.y + indicator.height <= header.y + header.height);
  // Sustained control input gives priority to the sidebar without queuing frames.
  const requestsDuringInteraction = await page.evaluate(async () => {
    const start = window.__rasterRequests.length;
    for (let i = 0; i < 8; i++) {
      document.querySelector('#controls').dispatchEvent(new PointerEvent('pointermove', { bubbles: true }));
      await new Promise(resolve => setTimeout(resolve, 50));
    }
    return window.__rasterRequests.length - start;
  });
  assert.ok(requestsDuringInteraction <= 1, 'sidebar interaction should defer new preview frames');
  await page.waitForTimeout(350);
  console.log('Native 300-GIF mode, low-FPS indicator, and sidebar priority passed');
  await page.locator('#generatorSmoothPreviewToggle').uncheck({ force: true });
  // Small export fixture: mode must not prescribe layer omissions or crop escapes.
  await page.evaluate(async () => {
    document.querySelector('#generatorCountSlider').value = '12';
    document.querySelector('#generatorCanvasWidthInput').value = '320';
    document.querySelector('#generatorCanvasHeightInput').value = '320';
    document.querySelector('#generatorSequenceEnabledToggle').checked = false;
    await window.GeneratorApp.generate(0x12345678);
  });
  await page.waitForFunction(() => window.GeneratorApp.getSummary().previewRenderer === 'dom');
  const runExport = async (flashing, format = 'webp') => page.evaluate(async ({ flashing, format }) => {
    const toggle = document.querySelector('#generatorSmoothPreviewToggle');
    toggle.checked = !flashing; toggle.dispatchEvent(new Event('change', { bubbles: true }));
    window.__rasterRequests = [];
    const result = await (format === 'mp4' ? window.GeneratorApp.exportMp4 : window.GeneratorApp.exportWebp)({ download: false, returnBlob: true });
    if (!result) throw new Error(document.querySelector('#generatorActionStatus').textContent);
    const hash = Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', await result.blob.arrayBuffer()))).map(n => n.toString(16).padStart(2, '0')).join('');
    const { blob, ...metadata } = result;
    return { hash, metadata, frames: window.__rasterRequests };
  }, { flashing, format });
  const normal = await runExport(false);
  assert.ok(normal.frames.every(frame => frame.count === 12 && frame.overlayCount === 0));
  const native = await runExport(true);
  assert.equal(native.hash, normal.hash, 'native preview must not add artificial glitches to export');
  assert.ok(native.frames.every(frame => frame.count === 12 && frame.overlayCount === 0));
  assert.equal(native.metadata.flashing, false);
  assert.equal(native.metadata.lossless, true);
  const mp4 = await runExport(true, 'mp4');
  assert.equal(mp4.metadata.frameCount, 180);
  assert.ok(mp4.frames.every(frame => frame.count === 12 && frame.overlayCount === 0));
  await page.reload({ waitUntil: 'load' });
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count === 12);
  assert.equal(await page.locator('#generatorSmoothPreviewToggle').isChecked(), false);
  assert.deepEqual(errors, []);
  console.log('Native mode, clean WebP/MP4 parity, default-off, and persistence checks passed');
} catch (error) {
  console.error(await page.evaluate(() => ({ summary: window.GeneratorApp?.getSummary(), status: document.querySelector('#generatorActionStatus')?.textContent })));
  throw error;
} finally { await context.close(); await browser.close(); await new Promise(resolve => server.close(resolve)); }
