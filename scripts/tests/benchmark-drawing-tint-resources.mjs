import { execFileSync } from 'node:child_process';
import { chromium } from 'playwright';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { resolve, extname } from 'node:path';
import { fileURLToPath } from 'node:url';

const root = fileURLToPath(new URL('../../', import.meta.url));
const baselineRef = process.argv[2] || '9c62926';
const sources = [
  ['baseline', execFileSync('git', ['show', `${baselineRef}:app.js`], { cwd: root, encoding: 'utf8', maxBuffer: 5 * 1024 * 1024 })],
  ['optimized', await readFile(resolve(root, 'app.js'), 'utf8')]
];
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
try {
  const results = [];
  for (const [name, source] of sources) {
    const page = await browser.newPage();
    await page.route('**/app.js?*', async route => route.fulfill({ contentType: 'text/javascript', body: source + '\nwindow.testTint = { applyBrushTintStyle, tintFilterCache };' }));
    await page.goto(`http://127.0.0.1:${server.address().port}/`);
    await page.waitForFunction(() => window.testTint);
    const result = await page.evaluate(() => {
      const fixture = document.createElement('div');
      fixture.style.cssText = 'position:fixed;width:1px;height:1px;overflow:hidden;';
      document.body.append(fixture);
      const marks = Array.from({ length: 300 }, () => {
        const canvas = document.createElement('canvas'); canvas.width = canvas.height = 1;
        fixture.append(canvas); return canvas;
      });
      const initialCount = testTint.tintFilterCache.size;
      const start = performance.now();
      for (let frame = 0; frame < 120; frame++) {
        marks.forEach((mark, index) => testTint.applyBrushTintStyle(mark, false, {
          color: '#de50af', amountPercent: (frame * 300 + index + .1234567) / 360
        }));
      }
      return { updates: 36000, updateMs: Number((performance.now() - start).toFixed(1)), resources: testTint.tintFilterCache.size - initialCount };
    });
    results.push({ name, ...result });
    await page.close();
  }
  console.log(JSON.stringify({ baselineRef, note: 'Isolated tint DOM update work; not whole-scene FPS', results }, null, 2));
} finally { await browser.close(); await new Promise(resolve => server.close(resolve)); }
