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
try {
  await page.goto(url, { waitUntil: 'load' });
  await page.waitForFunction(() => GeneratorApp?.getSummary().count === 120);
  await page.evaluate(() => {
    document.querySelector('#generatorCountSlider').value = '2';
    document.querySelector('#generatorCanvasWidthInput').value = '320';
    document.querySelector('#generatorCanvasHeightInput').value = '320';
    document.querySelector('#generatorSequenceEnabledToggle').checked = false;
  });
  for (let index = 0; index < 3; index++) {
    await page.evaluate(async index => { document.querySelector('#generatorCountSlider').value = String([3, 1, 2][index]); await GeneratorApp.generate(123 + index); }, index);
    await page.locator('#generatorBookmarkButton').click();
    await page.waitForFunction(count => GeneratorApp.getSummary().bookmarkCount === count, index + 1);
  }
  const original = await page.evaluate(() => GeneratorApp.getSummary().signature);
  await page.locator('#generatorBookmarkGalleryModeButton').click();
  await page.evaluate(async () => {
    window.testDir = await (await navigator.storage.getDirectory()).getDirectoryHandle('batch-output', {create:true});
    window.fileOrder = [];
    window.showDirectoryPicker = async () => ({
      name: 'batch-output',
      async getFileHandle(name, options) { if (options?.create) fileOrder.push(name); return testDir.getFileHandle(name, options); },
      removeEntry(name) { return testDir.removeEntry(name); }
    });
    const Native = Worker;
    window.failureInjected = false;
    window.Worker = class extends Native {
      postMessage(message, ...args) {
        if (!window.failureInjected && message.type === 'render-frame') {
          window.failureInjected = true;
          queueMicrotask(() => this.dispatchEvent(new MessageEvent('message', {data: {protocol:'brush-export-raster',version:1,type:'error',requestId:message.requestId,error:{message:'Injected worker failure'}}})));
          return;
        }
        return super.postMessage(message, ...args);
      }
    };
  });
  const open = async () => {
    await page.locator('#generatorExportAllButton').click();
    await page.locator('#generatorExportDuration').fill('1');
  };
  const finish = async () => {
    await page.waitForFunction(() => !GeneratorApp.getSummary().batchExporting, null, {timeout:180000});
    assert.equal(await page.evaluate(() => GeneratorApp.getSummary().signature), original);
    assert.equal(await page.locator('.generator-bookmark-card[data-export-state="done"]').count(), 3);
  };
  const files = () => page.evaluate(async () => { const list=[];for await(const [name,handle] of testDir.entries())list.push({name,size:(await handle.getFile()).size});return list; });
  await open();
  assert.equal(await page.locator('#generatorExportSubmit').isDisabled(), true);
  await page.locator('#generatorExportChooseFolder').click();
  await page.locator('#generatorExportSubmit').click();
  assert.equal(await page.locator('#generatorExportDialog').isVisible(), false);
  await page.waitForFunction(() => document.querySelector('.generator-bookmark-export-progress:not([hidden])'));
  assert.equal(await page.locator('#generatorBookmarksPanel').evaluate(el => el.closest('[inert]') === null), true);
  await finish();
  assert.equal(await page.evaluate(() => failureInjected), true);
  assert.equal((await files()).length, 3);
  assert.deepEqual(await page.evaluate(() => fileOrder.map(name => name.split('-')[1])), ['0000007b', '0000007c', '0000007d']);
  assert.ok((await files()).every(f => f.size > 0));
  await open(); await page.locator('#generatorExportSubmit').click(); await finish();
  assert.match(await page.locator('#generatorBatchStatus').textContent(), /3 already saved/);
  assert.equal((await files()).length, 3);
  // Changed settings produce distinct outputs; realtime sharing is requested once.
  await open(); await page.locator('#generatorExportMode button[value="realtime"]').click();
  await page.locator('#generatorBatchOrder button[value="gif-count"]').click();
  assert.equal(await page.locator('#generatorBatchOrder button[value="gif-count"]').getAttribute('aria-pressed'), 'true');
  await page.locator('#generatorExportSubmit').click(); await finish();
  assert.equal(await page.evaluate(() => captureTest.calls.length), 1);
  assert.equal(await page.evaluate(() => captureTest.streams.every(s=>s.getTracks().every(t=>t.readyState==='ended'))), true);
  assert.equal((await files()).length, 6);
  assert.deepEqual(await page.evaluate(() => fileOrder.slice(3).map(name => name.split('-')[1])), ['0000007c', '0000007d', '0000007b']);
  // Quality uses the same sequential queue and distinct filenames.
  await open(); await page.locator('#generatorExportMode button[value="quality"]').click();
  await page.locator('#generatorExportSubmit').click(); await finish();
  assert.equal((await files()).length, 9);
  assert.equal((await files()).filter(f=>f.name.endsWith('-quality.mp4')).length, 3);
  await open(); await page.locator('#generatorExportSubmit').click(); await finish();
  assert.match(await page.locator('#generatorBatchStatus').textContent(), /3 already saved/);
  assert.equal((await files()).length, 9);
  // Cancel while a different format is queued; current composition is restored.
  await open(); await page.locator('#generatorExportMode button[value="normal"]').click();
  await page.locator('#generatorExportFormat button[value="webp"]').click();
  await page.locator('#generatorExportSubmit').click();
  await page.locator('#generatorBatchCancel').click();
  await page.waitForFunction(() => !GeneratorApp.getSummary().batchExporting);
  assert.match(await page.locator('#generatorBatchStatus').textContent(), /cancelled/);
  assert.equal(await page.evaluate(() => GeneratorApp.getSummary().signature), original);
  await page.locator('#generatorBookmarkGalleryModeButton').click();
  await page.locator('#generatorDownloadButton').click();
  assert.equal(await page.locator('#generatorBatchOrderOptions').isVisible(), false);
  assert.deepEqual(errors, []);
  console.log('Batch regression passed: normal/realtime/quality queue, retry, duplicate skip, folder outputs, sidebar access, cancellation and original preview restoration.');
} finally { await context.close(); await browser.close(); await new Promise(resolve => server.close(resolve)); }
