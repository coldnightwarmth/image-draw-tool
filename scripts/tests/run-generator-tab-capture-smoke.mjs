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
const browser = await chromium.launch({ headless: true, channel: "chromium", args: ["--auto-accept-this-tab-capture"] });
const context = await browser.newContext({ viewport: { width: 1280, height: 900 }, acceptDownloads: true });
const page = await context.newPage();
page.setDefaultTimeout(30000);
const errors = [];
page.on('pageerror', error => errors.push(error.message));
// The test-only Chromium flag accepts sharing this isolated test tab only.
// Capture, cropping and recording are real browser APIs, without fixture streams.
await page.addInitScript(() => {
  window.testCaptureStreams = [];
  const capture = navigator.mediaDevices.getDisplayMedia.bind(navigator.mediaDevices);
  navigator.mediaDevices.getDisplayMedia = async options => {
    const stream = await capture(options);
    window.testCaptureStreams.push(stream);
    return stream;
  };
});
try {
  await page.goto(url, { waitUntil: 'load' });
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count === 120 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
  await page.evaluate(async () => {
    document.querySelector('#generatorCountSlider').value = '4';
    await window.GeneratorApp.generate(0xabcdef01);
  });
  // A deterministic moving patch lets us detect frozen captures, not just a valid header.
  await page.evaluate(() => {
    const patch = document.createElement('div');
    Object.assign(patch.style, { position: 'absolute', left: '10px', top: '10px', width: '80px', height: '80px', zIndex: '99999' });
    document.querySelector('#generatorCanvas').append(patch);
    const start = performance.now();
    const update = () => { const t = (performance.now() - start) / 1000; patch.style.background = `rgb(${Math.floor(t * 31) % 256},${Math.floor(t * 67) % 256},100)`; requestAnimationFrame(update); };
    update();
  });
  await page.locator('#generatorDownloadButton').click();
  await page.locator('#generatorExportMode button[value="realtime"]').click();
  await page.locator('#generatorExportDuration').fill('15');
  const downloadPromise = page.waitForEvent('download', { timeout: 120000 });
  await page.locator('#generatorExportSubmit').click({ force: true });
  const download = await downloadPromise;
  await page.waitForFunction(() => !window.GeneratorApp.getSummary().exporting);
  const metadata = await page.evaluate(() => window.GeneratorApp.getSummary().lastExport);
  assert.equal(metadata.realtime, true);
  assert.equal(metadata.captureArea, 'canvas');
  assert.ok(metadata.durationMs >= 14900 && metadata.durationMs < 20000);
  const bytes = await readFile(await download.path());
  assert.ok(bytes.length > 1000);
  const videoSize = await page.evaluate(async base64 => {
    const video = document.createElement('video'); video.muted = true;
    video.src = `data:video/mp4;base64,${base64}`;
    await new Promise((resolve, reject) => { video.onloadeddata = resolve; video.onerror = reject; });
    const canvas = document.createElement('canvas'); canvas.width = video.videoWidth; canvas.height = video.videoHeight;
    const ctx = canvas.getContext('2d');
    const samples = [];
    for (const time of [0.5, 3, 6, 9, 12, 14]) {
      await new Promise((resolve, reject) => { video.onseeked = resolve; video.onerror = reject; video.currentTime = time; });
      ctx.drawImage(video, 0, 0);
      samples.push(Array.from(ctx.getImageData(30, 30, 1, 1).data).join(','));
    }
    const size = { width: video.videoWidth, height: video.videoHeight, duration: video.duration, samples };

    video.pause(); video.removeAttribute('src'); video.load();
    return size;
  }, bytes.toString('base64'));
  assert.ok(Number.isFinite(videoSize.duration) && Math.abs(videoSize.duration - 15) < 0.5);
  assert.ok(new Set(videoSize.samples).size >= 5, `Frozen capture: ${videoSize.samples}`);
  assert.ok(videoSize.width > 0 && videoSize.width < 1280);
  assert.ok(videoSize.height > 0 && videoSize.height < 900);
  assert.equal(await page.evaluate(() => testCaptureStreams.length === 1 && testCaptureStreams.every(s => s.getTracks().every(t => t.readyState === 'ended'))), true);
  assert.deepEqual(errors, []);
  await page.screenshot({ path: '/tmp/generator-live-capture-ui.png' });
  console.log('Actual browser tab capture passed:', JSON.stringify({ ...metadata, playback: videoSize }));
} catch (error) {
  console.error('Capture status:', await page.locator('#generatorExportStatus').textContent());
  throw error;
} finally { await context.close(); await browser.close(); await new Promise(resolve => server.close(resolve)); }
