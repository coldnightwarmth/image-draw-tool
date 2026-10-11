import assert from 'node:assert/strict';
import { chromium } from 'playwright';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { resolve, extname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../../', import.meta.url));
const server = createServer(async (req, res) => {
  try {
    let path = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
    if (path.endsWith('/')) path += 'index.html';
    path = resolve(root, '.' + path);
    if (!path.startsWith(root)) throw Error('Invalid path');
    const data = await readFile(path);
    res.writeHead(200, { 'Content-Type': ({ '.js': 'text/javascript', '.html': 'text/html', '.css': 'text/css', '.gif': 'image/gif', '.wasm': 'application/wasm' })[extname(path)] || 'application/octet-stream' });
    res.end(data);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise(r => server.listen(0, '127.0.0.1', r));
const browser = await chromium.launch({ headless: true, ...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH ? { executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH } : {}) });
const page = await browser.newPage();
const errors = [];
page.on('pageerror', error => errors.push(error.message));
await page.route('**/app.js?*', async route => {
  const response = await route.fetch();
  await route.fulfill({ response, body: (await response.text()) + '\nwindow.testTint = { state, tintFilterCache, elementTintFilters, applyBrushTintStyle, getTintMatrixValues, createSequenceExportSnapshot, restoreSequenceExportSnapshot };' });
});
try {
  await page.goto(`http://127.0.0.1:${server.address().port}/`);
  await page.waitForFunction(() => window.testTint);
  const results = await page.evaluate(async () => {
    const { applyBrushTintStyle: apply, getTintMatrixValues: values, tintFilterCache: cache, elementTintFilters: bindings } = testTint;
    const check = (value, message) => { if (!value) throw Error(message); };
    const tick = () => new Promise(resolve => setTimeout(resolve, 0));
    const fixture = document.createElement('div');
    fixture.style.cssText = 'position:fixed;left:0;top:0;width:64px;height:32px;z-index:999999;background:#111;';
    document.body.appendChild(fixture);
    const make = () => { const canvas = document.createElement('canvas'); canvas.width = canvas.height = 32; canvas.getContext('2d').fillStyle = '#31c897'; canvas.getContext('2d').fillRect(0, 0, 32, 32); fixture.appendChild(canvas); return canvas; };
    const first = make(), second = make();
    const initialCount = cache.size;
    const base = { color: '#abcdef', amountPercent: 32.134542134 };
    apply(first, false, base); apply(second, false, base);
    check(cache.size === initialCount + 1, 'Identical tints should share a single resource');
    const shared = bindings.get(first).resource;
    check(shared === bindings.get(second).resource && shared.references === 2, 'Shared reference count');
    const changed = { layers: [base, { color: '#feab25', amountPercent: 82.33455432342 }] };
    const expectedMatrix = values(changed).map(value => value.toFixed(6)).join(' ');
    fixture.append(first); await tick();
    check(bindings.get(first).resource === shared && shared.references === 2, 'Moving a connected stamp within one task must preserve ownership');
    first.remove(); apply(first, false, changed);
    check(shared.references === 1 && shared.matrixValues === values(base).map(value => value.toFixed(6)).join(' '), 'Changing a detached shared owner before observation preserves the other owner');
    fixture.append(first); await tick();
    check(bindings.get(first).resource.matrixValues === expectedMatrix, 'Reinserted changed owner preserves its new tint');
    apply(first, false, base);
    apply(second, false, changed);
    const initialStrokes = testTint.state.strokes;
    testTint.state.strokes = [{ elements: [first, second] }];
    const distinctSnapshot = testTint.createSequenceExportSnapshot();
    apply(second, false, base);
    check(bindings.get(first).resource === bindings.get(second).resource, 'Export fixture converges to a shared resource');
    testTint.restoreSequenceExportSnapshot(distinctSnapshot);
    testTint.state.strokes = initialStrokes;
    check(bindings.get(first).resource !== bindings.get(second).resource, 'Restoring distinct export tints must split a shared resource');
    check(bindings.get(second).resource.matrixValues === expectedMatrix && bindings.get(first).resource.matrixValues === values(base).map(value => value.toFixed(6)).join(' '), 'Export restore preserves both distinct colors');
    check(first.style.filter.includes(`#${bindings.get(first).resource.id}`) && second.style.filter.includes(`#${bindings.get(second).resource.id}`), 'Restored CSS points to each restored resource');
    apply(second, false, base);
    apply(first, true, changed, { blurAmount: 1.23 });
    check(bindings.get(first).resource !== shared, 'Changing one stamp must not alter another stamp');
    check(shared.matrixValues === values(base).map(value => value.toFixed(6)).join(' '), 'Untouched shared color');
    check(bindings.get(first).resource.matrixValues === expectedMatrix, 'Exact layered color matrix');
    check(first.style.filter.includes('grayscale(0.75)') && first.style.filter.includes('blur(1.23px)'), 'Other filter order preserved');
    const animatedResource = bindings.get(first).resource;
    for (let index = 0; index < 4000; index++) apply(first, false, { color: '#feab25', amountPercent: (index + .123456789) / 40 });
    check(bindings.get(first).resource === animatedResource, 'Changing exclusive tints should reuse a resource');
    check(cache.size === initialCount + 2, 'Thousands of frames must not grow resources');
    apply(first, false, base);
    check(bindings.get(first).resource === shared && cache.size === initialCount + 1, 'Converging colors should share and reclaim');
    first.remove(); await tick();
    check(shared.references === 1 && cache.size === initialCount + 1, 'Removed stamp releases its reference');
    second.remove(); await tick();
    check(cache.size === initialCount && !shared.element.isConnected, 'Last removed stamp releases SVG and cache');
    fixture.append(first); await tick();
    check(bindings.get(first).active && bindings.get(first).resource.element.isConnected, 'Undo/reinsertion restores tint resource');
    check(bindings.get(first).resource.matrixValues === values(base).map(value => value.toFixed(6)).join(' '), 'Reinsertion preserves exact color');
    const strokes = testTint.state.strokes;
    testTint.state.strokes = [{ elements: [first] }];
    const snapshot = testTint.createSequenceExportSnapshot();
    apply(first, false, changed);
    testTint.restoreSequenceExportSnapshot(snapshot);
    testTint.state.strokes = strokes;
    check(bindings.get(first).resource.matrixValues === values(base).map(value => value.toFixed(6)).join(' '), 'Export restores exact live tint after mutable matrix changes');
    apply(first, false, { amountPercent: 0 });
    check(cache.size === initialCount && !first.style.filter, 'Disabling tint reclaims resource');
    const detached = document.createElement('canvas');
    apply(detached, false, base);
    check(cache.size === initialCount && !bindings.get(detached).resource.element.isConnected, 'Detached new stamp does not retain a global resource');
    fixture.append(detached); await tick();
    check(bindings.get(detached).active && bindings.get(detached).resource.element.isConnected, 'New detached stamp activates on insertion');
    fixture.remove(); await tick();
    check(cache.size === initialCount, 'Removing a subtree releases its resources');
    fixture.replaceChildren();
    const marks = Array.from({ length: 300 }, () => { const canvas = document.createElement('canvas'); canvas.width = canvas.height = 1; fixture.append(canvas); return canvas; });
    document.body.append(fixture); await tick();
    const start = performance.now();
    for (let frame = 0; frame < 120; frame++) {
      marks.forEach((mark, index) => apply(mark, false, { color: '#de50af', amountPercent: (frame * 300 + index + .1234567) / 360 }));
    }
    const elapsedMs = performance.now() - start;
    const resources = cache.size - initialCount;
    check(resources === 300, `300 animated stamps must retain only 300 resources across 36,000 color updates: ${resources}`);
    fixture.remove(); await tick();
    check(cache.size === initialCount, 'Stress fixture leaves no resources behind');
    return { updates: 36000, elapsedMs: Math.round(elapsedMs), liveResources: resources, exactMatrix: expectedMatrix };
  });
  // Compare actual browser paint after an in-place matrix change against an
  // immutable reference filter, including alpha, stacked tints, and effect order.
  await page.evaluate(() => {
    const fixture = document.createElement('div');
    fixture.id = 'tint-pixel-fixture';
    fixture.style.cssText = 'position:fixed;left:20px;top:20px;z-index:999999;background:white;display:flex;gap:40px;padding:20px;';
    for (const id of ['tint-live', 'tint-reference']) {
      const canvas = document.createElement('canvas'); canvas.id = id; canvas.width = canvas.height = 32;
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#31c897'; ctx.fillRect(0, 0, 16, 32);
      ctx.fillStyle = 'rgba(230,45,150,.35)'; ctx.fillRect(16, 0, 16, 32);
      fixture.append(canvas);
    }
    document.body.append(fixture);
    const live = document.getElementById('tint-live');
    testTint.applyBrushTintStyle(live, false, { color: '#abc123', amountPercent: 60 });
  });
  const before = await page.locator('#tint-live').screenshot();
  await page.evaluate(() => {
    const settings = { layers: [{ color: '#2174df', amountPercent: 18.756724 }, { color: '#fa7528', amountPercent: 49.1234432323 }] };
    const live = document.getElementById('tint-live');
    testTint.applyBrushTintStyle(live, true, settings, { blurAmount: .25 });
    const filter = document.createElementNS('http://www.w3.org/2000/svg', 'filter');
    filter.id = 'test-immutable-tint'; filter.setAttribute('color-interpolation-filters', 'sRGB');
    const matrix = document.createElementNS('http://www.w3.org/2000/svg', 'feColorMatrix');
    matrix.setAttribute('type', 'matrix');
    matrix.setAttribute('values', testTint.getTintMatrixValues(settings).map(value => value.toFixed(6)).join(' '));
    filter.append(matrix); document.querySelector('#filterDefs defs').append(filter);
    document.getElementById('tint-reference').style.filter = 'grayscale(0.75) url(#test-immutable-tint) blur(0.25px)';
  });
  const livePixels = await page.locator('#tint-live').screenshot();
  const referencePixels = await page.locator('#tint-reference').screenshot();
  assert.notDeepEqual(before, livePixels, 'Updating an existing matrix must update visible pixels');
  assert.deepEqual(livePixels, referencePixels, 'Mutable and immutable SVG tint filters must paint identical pixels');
  assert.equal(errors.length, 0, errors.join('\n'));
  console.log('PASS exact shared/mutable tint, removal/undo, export restoration, pixel-identical browser paint, and bounded 300-stamp animation resources');
  console.log(JSON.stringify(results));
} finally { await browser.close(); await new Promise(resolve => server.close(resolve)); }
