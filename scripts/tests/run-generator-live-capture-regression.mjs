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
const context = await browser.newContext({ viewport: { width: 1280, height: 900 }, acceptDownloads: true });
const page = await context.newPage();
page.setDefaultTimeout(30000);
const errors = [];
page.on('pageerror', error => errors.push(error.message));
await page.addInitScript(() => {
  window.captureTest = { calls: [], streams: [], scenario: 'canvas', cropCalls: 0 };
  const test = window.captureTest;
  const NativeRecorder = window.MediaRecorder;
  Object.defineProperty(window, 'CropTarget', { configurable: true, value: {
    async fromElement(element) { test.targetId = element.id; return {}; }
  } });
  // Permission chooser is mocked; recording/muxing/download/playback use the
  // real browser MediaRecorder with a changing video-only fixture stream.
  const makeStream = () => {
    const canvas = document.createElement('canvas'); canvas.width = 160; canvas.height = 100;
    const ctx = canvas.getContext('2d'); let frame = 0;
    const timer = setInterval(() => { ctx.fillStyle = frame++ % 2 ? '#ef3020' : '#123456'; ctx.fillRect(0, 0, 160, 100); }, 30);
    const stream = canvas.captureStream(30);
    const track = stream.getVideoTracks()[0];
    const originalStop = track.stop.bind(track);
    track.stop = () => { clearInterval(timer); originalStop(); };
    const settings = track.getSettings.bind(track);
    track.getSettings = () => ({ ...settings(), displaySurface: test.scenario === 'screen' ? 'monitor' : 'browser' });
    if (test.scenario !== 'tab') track.cropTo = async () => {
      test.cropCalls++;
      if (test.scenario === 'crop-failed') throw new Error('Wrong tab');
    };
    test.streams.push(stream);
    return stream;
  };
  navigator.mediaDevices.getDisplayMedia = options => {
    test.calls.push(options);
    if (test.scenario === 'denied') return Promise.reject(new DOMException('Permission denied', 'NotAllowedError'));
    if (test.scenario === 'pending') return new Promise(resolve => { test.grant = () => resolve(makeStream()); });
    return Promise.resolve(makeStream());
  };
  window.MediaRecorder = class extends NativeRecorder {
    constructor(...args) {
      if (test.scenario === 'recorder-failed') throw new Error('Injected encoder failure');
      super(...args);
      if (test.scenario === 'runtime-error') this.addEventListener('start', () => setTimeout(() => this.dispatchEvent(new Event('error')), 30), { once: true });
    }
  };
});
const assertReleased = async () => {
  assert.equal(await page.evaluate(() => captureTest.streams.every(stream => stream.getTracks().every(track => track.readyState === 'ended'))), true);
  assert.equal(await page.evaluate(() => window.GeneratorApp.getSummary().exporting), false);
  assert.equal(await page.locator('#generatorSmoothPreviewToggle').isDisabled(), false);
};
const playBlob = async () => page.evaluate(async () => {
  const result = window.lastCaptureResult;
  const objectUrl = URL.createObjectURL(result.blob);
  const video = document.createElement('video'); video.muted = true;
  try {
    await new Promise((resolve, reject) => {
      const timer = setTimeout(() => reject(new Error('video load timeout')), 10000);
      video.onloadeddata = () => { clearTimeout(timer); resolve(); };
      video.onerror = () => { clearTimeout(timer); reject(new Error('recorded video is invalid')); };
      video.src = objectUrl;
    });
    await video.play();
    return { width: video.videoWidth, height: video.videoHeight, type: result.blob.type, size: result.blob.size };
  } finally { video.pause(); video.removeAttribute('src'); video.load(); URL.revokeObjectURL(objectUrl); }
});
try {
  await page.goto(url, { waitUntil: 'load' });
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count === 120 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
  await page.evaluate(async () => {
    document.querySelector('#generatorCountSlider').value = '4';
    await window.GeneratorApp.generate(0xabcdef01);
  });
  assert.equal(await page.locator('#generatorSmoothPreviewToggle').isChecked(), false);
  assert.equal(await page.evaluate(() => GeneratorApp.getSummary().previewRenderer), 'dom');
  assert.equal(await page.locator('#generatorLiveCapturePanel').count(), 0);
  await page.locator('#generatorDownloadButton').click();
  assert.equal(await page.locator('#generatorExportDialog').isVisible(), true);
  assert.equal(await page.locator('#generatorExportDestination').textContent(), 'Downloads');
  assert.equal(await page.locator('#generatorExportDuration').inputValue(), '6');
  assert.equal(await page.locator('#generatorExportFormat').getAttribute('data-value'), 'mp4');
  assert.equal(await page.locator('#generatorExportMode').getAttribute('data-value'), 'normal');
  await page.locator('#generatorExportMode button[value="realtime"]').click();
  assert.equal(await page.evaluate(() => captureTest.calls.length), 0, 'opening options must never request sharing');
  // Six-second automatic completion and actual downloadable media.
  const downloadPromise = page.waitForEvent('download');
  await page.locator('#generatorExportSubmit').click({ force: true });
  await page.waitForFunction(() => !document.querySelector('#generatorLiveCaptureFinish').disabled);
  assert.equal(await page.locator('#generatorSmoothPreviewToggle').isDisabled(), true);
  assert.equal(await page.locator('#generatorExportDialog').isVisible(), false);
  const download = await downloadPromise;
  assert.match(download.suggestedFilename(), /-live\.mp4$/);
  await page.waitForFunction(() => !window.GeneratorApp.getSummary().exporting);
  const metadata = await page.evaluate(() => window.GeneratorApp.getSummary().lastExport);
  assert.equal(metadata.realtime, true);
  assert.equal(metadata.captureArea, 'canvas');
  assert.ok(metadata.durationMs >= 5900 && metadata.durationMs < 10000);
  assert.equal(await page.evaluate(() => captureTest.targetId), 'generatorCanvas');
  assert.equal(await page.evaluate(() => captureTest.calls[0].audio), false);
  assert.equal(await page.evaluate(() => captureTest.calls[0].preferCurrentTab), true);
  await assertReleased();
  await page.locator('#generatorExportClose').click();
  // Full-tab fallback, early finish, and playback of the real encoded blob.
  await page.evaluate(() => {
    captureTest.scenario = 'tab';
    window.capturePromise = window.GeneratorApp.captureLive({ download: false, returnBlob: true }).then(result => { window.lastCaptureResult = result; return result; });
  });
  await page.waitForFunction(() => !document.querySelector('#generatorLiveCaptureFinish').disabled);
  await page.waitForTimeout(500);
  await page.locator('#generatorLiveCaptureFinish').click({ force: true });
  const early = await page.evaluate(async () => { const { blob, ...result } = await capturePromise; return result; });
  assert.equal(early.captureArea, 'tab'); assert.ok(early.durationMs < 5000);
  const playback = await playBlob();
  assert.equal(playback.width, 160); assert.equal(playback.height, 100); assert.ok(playback.size > 0);
  await assertReleased();
  // Permission denied, wrong surface/crop, and synchronous/asynchronous recorder failures.
  for (const scenario of ['denied', 'screen', 'crop-failed', 'recorder-failed', 'runtime-error']) {
    const result = await page.evaluate(async scenario => {
      captureTest.scenario = scenario;
      return window.GeneratorApp.captureLive({ download: false });
    }, scenario);
    assert.equal(result, null, scenario);
    await assertReleased();
  }
  // Cancel an open permission dialog; late permission must immediately close tracks.
  await page.evaluate(() => {
    captureTest.scenario = 'pending';
    window.capturePromise = window.GeneratorApp.captureLive({ download: false });
  });
  await page.locator('#generatorExportCancelButton').click({ force: true });
  assert.equal(await page.evaluate(() => capturePromise), null);
  await page.evaluate(() => captureTest.grant());
  await page.waitForTimeout(50);
  await assertReleased();
  // Cancel active recording through the shared escape/cancel path.
  await page.evaluate(() => {
    captureTest.scenario = 'canvas';
    window.capturePromise = window.GeneratorApp.captureLive({ download: false });
  });
  await page.waitForFunction(() => !document.querySelector('#generatorLiveCaptureFinish').disabled);
  await page.keyboard.press('Escape');
  assert.equal(await page.evaluate(() => capturePromise), null);
  await assertReleased();
  // Browser 'stop sharing' saves the captured portion and releases everything.
  await page.evaluate(() => {
    window.capturePromise = window.GeneratorApp.captureLive({ download: false });
  });
  await page.waitForFunction(() => !document.querySelector('#generatorLiveCaptureFinish').disabled);
  await page.waitForTimeout(300);
  await page.evaluate(() => captureTest.streams.at(-1).getVideoTracks()[0].dispatchEvent(new Event('ended')));
  assert.ok(await page.evaluate(() => capturePromise));
  await assertReleased();
  // Leaving the page aborts recording and releases the sharing track.
  await page.evaluate(() => {
    window.capturePromise = window.GeneratorApp.captureLive({ download: false });
  });
  await page.waitForFunction(() => !document.querySelector('#generatorLiveCaptureFinish').disabled);
  await page.evaluate(() => window.dispatchEvent(new PageTransitionEvent('pagehide')));
  assert.equal(await page.evaluate(() => capturePromise), null);
  await assertReleased();
  // WebP conversion preserves the captured stream and the requested duration.
  const capturedWebp = await page.evaluate(async () => {
    const result = await GeneratorApp.captureLive({ format: 'webp', durationSeconds: 1, download: false, returnBlob: true });
    if (!result) throw new Error(document.querySelector('#generatorExportStatus').textContent);
    const decoder = new ImageDecoder({ data: await result.blob.arrayBuffer(), type: 'image/webp' });
    await decoder.tracks.ready;
    const first = (await decoder.decode({ frameIndex: 0 })).image;
    const details = { format: result.format, duration: result.durationMs, frames: decoder.tracks.selectedTrack.frameCount, width: first.displayWidth, height: first.displayHeight };
    first.close(); decoder.close();
    return details;
  });
  assert.equal(capturedWebp.format, 'live-webp');
  assert.ok(capturedWebp.duration >= 1000 && capturedWebp.duration < 2000);
  assert.ok(capturedWebp.frames >= 20);
  assert.equal(capturedWebp.width, 160); assert.equal(capturedWebp.height, 100);
  await assertReleased();
  // Exercise actual File System Access writes in this isolated origin's sandbox.
  // Only the native folder chooser is substituted; no desktop folder is accessed.
  await page.evaluate(async () => {
    const root = await navigator.storage.getDirectory();
    window.testExportDirectory = await root.getDirectoryHandle('export-test', { create: true });
    window.showDirectoryPicker = async options => { window.pickerOptions = options; return testExportDirectory; };
  });
  await page.locator('#generatorDownloadButton').click();
  await page.locator('#generatorExportChooseFolder').click();
  await page.waitForFunction(() => document.querySelector('#generatorExportDestination').textContent === 'export-test');
  assert.equal(await page.evaluate(() => pickerOptions.startIn), 'downloads');
  await page.locator('#generatorExportDuration').fill('1');
  for (let count = 1; count <= 2; count++) {
    await page.locator('#generatorExportSubmit').click();
    await page.waitForFunction(() => !GeneratorApp.getSummary().exporting);
    const files = await page.evaluate(async () => {
      const entries = [];
      for await (const [name, handle] of testExportDirectory.entries()) entries.push({ name, size: (await handle.getFile()).size });
      return entries;
    });
    assert.equal(files.length, count);
    assert.ok(files.every(file => file.size > 100));
    if (count === 2) assert.ok(files.some(file => file.name.includes(' (1).mp4')));
    assert.equal(await page.locator('#generatorExportDialog').isVisible(), true);
  }
  await page.screenshot({ path: '/tmp/generator-export-menu-desktop.png' });
  await page.setViewportSize({ width: 390, height: 844 });
  const dialog = await page.locator('#generatorExportDialog').boundingBox();
  assert.ok(dialog.x >= 0 && dialog.x + dialog.width <= 390);
  assert.ok(dialog.y >= 0 && dialog.y + dialog.height <= 844);
  await page.screenshot({ path: '/tmp/generator-export-menu-mobile.png' });
  await page.setViewportSize({ width: 1280, height: 900 });
  // Picker cancellation preserves the prior destination; revoked write access reports failure.
  await page.evaluate(() => { window.showDirectoryPicker = async () => { throw new DOMException('cancelled', 'AbortError'); }; });
  await page.locator('#generatorExportChooseFolder').click();
  await page.waitForFunction(() => !document.querySelector('#generatorExportSettings').disabled);
  assert.equal(await page.locator('#generatorExportDestination').textContent(), 'export-test');
  await page.locator('#generatorExportResetFolder').click();
  await page.locator('#generatorExportClose').click();
  const failedWrite = await page.evaluate(async () => {
    const directoryHandle = { async getFileHandle() { throw new DOMException('Folder permission revoked', 'NotAllowedError'); } };
    return GeneratorApp.captureLive({ durationSeconds: 1, directoryHandle });
  });
  assert.equal(failedWrite, null);
  await assertReleased();
  // Realtime capture must leave an opted-in smooth preview running.
  await page.locator('#generatorSmoothPreviewToggle').check({ force: true });
  await page.waitForFunction(() => GeneratorApp.getSummary().previewFrames >= 2);
  const smooth = await page.evaluate(async () => {
    const before = GeneratorApp.getSummary().previewFrames;
    const result = await GeneratorApp.captureLive({ durationSeconds: 1, download: false });
    return { result, before, after: GeneratorApp.getSummary().previewFrames, renderer: GeneratorApp.getSummary().previewRenderer };
  });
  assert.ok(smooth.result); assert.equal(smooth.renderer, 'worker'); assert.ok(smooth.after > smooth.before);
  await page.locator('#generatorSmoothPreviewToggle').uncheck({ force: true });
  await page.locator('#generatorDownloadButton').click();
  await page.evaluate(() => { navigator.mediaDevices.getDisplayMedia = undefined; });
  await page.locator('#generatorExportMode button[value="normal"]').click();
  await page.locator('#generatorExportMode button[value="realtime"]').click();
  assert.equal(await page.locator('#generatorExportSubmit').isDisabled(), true);
  assert.match(await page.locator('#generatorExportSubmit').getAttribute('title'), /unavailable/);
  assert.deepEqual(errors, []);
  console.log('Live capture regression passed: six-second download, playback, crop/full-tab modes, early finish, cancel/denial, recorder errors, late permission, and stream cleanup.');
} finally { await context.close(); await browser.close(); await new Promise(resolve => server.close(resolve)); }
