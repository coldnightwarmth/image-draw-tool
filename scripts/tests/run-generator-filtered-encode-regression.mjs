#!/usr/bin/env node
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { resolve, extname, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = fileURLToPath(new URL('../../', import.meta.url));
const mime = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.css': 'text/css', '.gif': 'image/gif', '.wasm': 'application/wasm' };
let fixture;
const server = createServer(async (req, res) => {
  try {
    let pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
    if (pathname.endsWith('/')) pathname += 'index.html';
    const path = resolve(root, `.${pathname}`);
    if (!path.startsWith(resolve(root) + sep)) throw new Error('Invalid path');
    const data = pathname === '/brushes/quality-fixture.gif' && fixture ? fixture : await readFile(path);
    res.writeHead(200, { 'Content-Type': mime[extname(path)] || 'application/octet-stream' });
    res.end(data);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const url = `http://127.0.0.1:${server.address().port}/generator/?seed=1234abcd`;
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ viewport: { width: 1280, height: 900 }, acceptDownloads: true });
const page = await context.newPage();
page.setDefaultTimeout(30000);
const errors = [];
page.on('pageerror', error => errors.push(error.message));
try {
  if (process.env.QUALITY_FORCE_MESSAGE_CHANNEL) await page.route('**/export-raster-worker.js?*', async route => {
    const response=await route.fetch();
    await route.fulfill({response,body:(await response.text()).replace('if (globalThis.scheduler?.yield)', 'if (false)')});
  });
  await page.route('**/generator.js?*', async route => {
    const response = await route.fetch();
    const source = (await response.text()).replace('  window.GeneratorApp = {',
      '  window.qualityTest = { state, getGeneratorQualityMp4EncoderConfig, createGeneratorExportScene, createGeneratorLoopPlan, createGeneratorRasterSession, renderGeneratorFramePixels };\n  window.GeneratorApp = {');
    await route.fulfill({ response, body: source });
  });
  await page.goto(url, {waitUntil:'load'});
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count > 0 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
  console.log('Config:', await page.evaluate(() => qualityTest.getGeneratorQualityMp4EncoderConfig(320,320)));
  await page.addScriptTag({url:'/gif.js'});
  fixture = Buffer.from(await page.evaluate(async () => {
    const gif = new GIF({workers:1, workerScript:'/gif.worker.js', width:64, height:64, quality:1, dither:false, repeat:0});
    let seed=42;
    for(let index=0;index<12;index++) {
      const pixels=new Uint8ClampedArray(64*64*4);
      for(let p=0;p<pixels.length;p+=4) {
        seed=(Math.imul(seed,1664525)+1013904223)>>>0;
        pixels[p]=pixels[p+1]=pixels[p+2]=seed>>>24; pixels[p+3]=255;
      }
      gif.addFrame(new ImageData(pixels,64,64),{delay:20});
    }
    return new Promise((resolve,reject)=>{gif.on('finished',async blob=>resolve(Array.from(new Uint8Array(await blob.arrayBuffer()))));gif.on('abort',reject);gif.render();});
  }));
  console.log('Fixture bytes:',fixture.length);
  const result = await page.evaluate(async () => {
    const {state} = qualityTest;
    state.currentWidth=320;state.currentHeight=320;state.currentMargin=8;state.currentMarginMode='crop';
    state.currentBackground='#123456';state.currentCount=24;
    const base=state.currentSpecs[0];
    state.currentSpecs=Array.from({length:24},(_,i)=>({...base,index:i,motifId:i,x:16+(i%20)*16,y:10+Math.floor(i/20)*21,
      width:32,height:32,opacity:1,rotation:0,tintAmount:.6,filter:'sepia(0.4) saturate(3) hue-rotate(120deg)',uncropped:i%15===0,markTransform:null,
      brush:{...base.brush,source:'brushes/quality-fixture.gif'},sequence:{effect:'rotate',duration:800,rotationAmount:360,delay:0,motifId:i,timing:'all'}}));
    window.exportFixtures={};
    const output=[];
    for(const mode of ['normal','quality']) {
      const result=await GeneratorApp.exportMp4({mode,durationSeconds:1,download:false,returnBlob:true});
      if(!result)throw Error(document.querySelector('#generatorExportStatus').textContent);
      window.exportFixtures[mode]=result.blob;
      const {blob,...details}=result;output.push(details);
    }
    const webp=await GeneratorApp.exportWebp({mode:'quality',durationSeconds:1,download:false,returnBlob:true});
    if(!webp)throw Error(document.querySelector('#generatorExportStatus').textContent);
    window.exportFixtures.webp=webp.blob;
    const {blob,...details}=webp;output.push(details);
    return output;
  });
  console.log('Exports:',JSON.stringify(result));
  assert.equal(result[0].fps,30);
  assert.equal(result[1].fps,60);
  assert.equal(result[1].renderingMode,'quality');
  assert.equal(result[2].lossless,true);
  assert.equal(result[2].frameCount,50);
  const decoded=await page.evaluate(async()=>{
    const results=[];
    for(const mode of ['normal','quality']) {
      const video=document.createElement('video');video.muted=true;const url=URL.createObjectURL(exportFixtures[mode]);
      try {await new Promise((resolve,reject)=>{video.onloadeddata=resolve;video.onerror=()=>reject(Error('Invalid MP4'));video.src=url;});results.push({mode,duration:video.duration,width:video.videoWidth,height:video.videoHeight});}
      finally {video.removeAttribute('src');video.load();URL.revokeObjectURL(url);}
    }
    return results;
  });
  for(const result of decoded){assert(Math.abs(result.duration-1)<.025);assert.equal(result.width,320);assert.equal(result.height,320);}
  assert.equal(errors.length,0,errors.join('\n'));console.log('PASS complete filtered normal/quality MP4 and WebP exports',decoded);
} finally {await browser.close();await new Promise(resolve=>server.close(resolve));}
