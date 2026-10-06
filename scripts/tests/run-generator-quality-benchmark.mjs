#!/usr/bin/env node
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile } from 'node:fs/promises';
import { resolve, extname, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';

const root = fileURLToPath(new URL('../../', import.meta.url));
const mime = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.css': 'text/css', '.gif': 'image/gif', '.wasm': 'application/wasm' };
const scenario = process.env.QUALITY_BENCHMARK_CASE || 'busy';
const settings = {
  busy: { width: 320, height: 320, count: 300, sources: 1, sourceSize: 64, gifFrames: 12, animate: true },
  large: { width: 1200, height: 800, count: 300, sources: 32, sourceSize: 128, gifFrames: 12, animate: true },
  still: { width: 1200, height: 800, count: 4, sources: 1, sourceSize: 128, gifFrames: 1, animate: false }
}[scenario];
assert.ok(settings, 'Use QUALITY_BENCHMARK_CASE=busy, large or still');
const formats = (process.env.QUALITY_BENCHMARK_FORMATS || 'mp4,webp').split(',');
let fixture;
const server = createServer(async (req, res) => {
  try {
    let pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname);
    if (pathname.endsWith('/')) pathname += 'index.html';
    const path = resolve(root, `.${pathname}`);
    if (!path.startsWith(resolve(root) + sep)) throw new Error('Invalid path');
    const baselinePath = process.env.QUALITY_BASELINE_DIR && resolve(process.env.QUALITY_BASELINE_DIR, `.${pathname}`);
    const data = /^\/brushes\/quality-fixture(?:-\d+)?\.gif$/.test(pathname) && fixture ? fixture : await (baselinePath ? readFile(baselinePath).catch(()=>readFile(path)) : readFile(path));
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
  await page.route('**/generator.js?*', async route => {
    const response = await route.fetch();
    const source = (await response.text()).replace('  window.GeneratorApp = {',
      '  window.qualityTest = { state, getGeneratorQualityMp4EncoderConfig, createGeneratorExportScene, createGeneratorLoopPlan, createGeneratorRasterSession, renderGeneratorFramePixels };\n  window.GeneratorApp = {');
    await route.fulfill({ response, body: source });
  });
  await page.goto(url, {waitUntil:'load'});
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count === 120 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
  console.log('Case:',scenario,settings);
  console.log('Config:', await page.evaluate(({width,height}) => qualityTest.getGeneratorQualityMp4EncoderConfig(width,height),settings));
  await page.addScriptTag({url:'/gif.js'});
  fixture = Buffer.from(await page.evaluate(async ({sourceSize,gifFrames}) => {
    const gif = new GIF({workers:1, workerScript:'/gif.worker.js', width:sourceSize, height:sourceSize, quality:1, dither:false, repeat:0});
    let seed=42;
    for(let index=0;index<gifFrames;index++) {
      const pixels=new Uint8ClampedArray(sourceSize*sourceSize*4);
      for(let p=0;p<pixels.length;p+=4) {
        seed=(Math.imul(seed,1664525)+1013904223)>>>0;
        pixels[p]=pixels[p+1]=pixels[p+2]=seed>>>24; pixels[p+3]=255;
      }
      gif.addFrame(new ImageData(pixels,sourceSize,sourceSize),{delay:20});
    }
    return new Promise((resolve,reject)=>{gif.on('finished',async blob=>resolve(Array.from(new Uint8Array(await blob.arrayBuffer()))));gif.on('abort',reject);gif.render();});
  },settings));
  console.log('Fixture bytes:',fixture.length);
  const result = await page.evaluate(async ({settings,formats}) => {
    const {width,height,count,sources,animate}=settings;
    const {state} = qualityTest;
    state.currentWidth=width;state.currentHeight=height;state.currentMargin=8;state.currentMarginMode='crop';
    state.currentBackground='#123456';state.currentCount=count;
    const base=state.currentSpecs[0];
    state.currentSpecs=Array.from({length:count},(_,i)=>({...base,index:i,motifId:i,x:(16+(i%20)*16)*width/320,y:(10+Math.floor(i/20)*21)*height/320,
      width:32*width/320,height:32*height/320,opacity:1,rotation:0,tintAmount:0,uncropped:i%15===0,markTransform:null,
      brush:{...base.brush,source:'brushes/quality-fixture'+(sources>1?'-'+i%sources:'')+'.gif'},
      sequence:animate?{effect:'rotate',duration:800,rotationAmount:360,delay:0,motifId:i,timing:'all'}:null}));
    window.exportFixtures={};
    const output=[];
    for(const format of formats) {
      const started=performance.now();
      const result=await GeneratorApp[format==='mp4'?'exportMp4':'exportWebp']({mode:'quality',durationSeconds:1,download:false,returnBlob:true});
      const elapsedMs=Math.round(performance.now()-started);
      if(!result)throw Error(document.querySelector('#generatorExportStatus').textContent);
      window.exportFixtures[format]=result.blob;
      const {blob,...details}=result;
      const sha256=Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',await blob.arrayBuffer())),v=>v.toString(16).padStart(2,'0')).join('');
      output.push({...details,elapsedMs,sha256});
    }
    // Hash source rasters too: compression effort may change encoded bytes,
    // while the exact crop/effect/source pixels must stay unchanged.
    const {createGeneratorLoopPlan,createGeneratorExportScene,createGeneratorRasterSession,renderGeneratorFramePixels}=qualityTest;
    const task={cancelled:false,quality:true},session=createGeneratorRasterSession(task);
    try {
      const specs=state.currentSpecs,dimensions={width,height},background=state.currentBackground;
      let plan=createGeneratorLoopPlan(specs,null,1000);
      const prepared=await session.prepare(createGeneratorExportScene(specs,dimensions,background,plan,true,true));
      if(prepared.assets.length!==sources||prepared.skippedAssets?.length)throw Error('Benchmark sources were not loaded');
      plan=createGeneratorLoopPlan(specs,new Map(prepared.assets.map(a=>[a.id,a.totalDurationMs])),1000);
      const hashes=[];
      for(const time of [0,1000/60,250,500,980]) {
        const pixels=await renderGeneratorFramePixels(session,specs.filter(s=>!s.uncropped),specs.filter(s=>s.uncropped),time,plan,dimensions,background);
        hashes.push(Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',pixels)),v=>v.toString(16).padStart(2,'0')).join(''));
      }
      output.push({rasterHashes:hashes});
      if(animate&&new Set(hashes).size<2)throw Error('Animated benchmark did not produce changing pixels');
    } finally {session.release();}
    return output;
  },{settings,formats});
  console.log('Exports:',JSON.stringify(result));
  assert.deepEqual(errors,[]);
} finally {await context.close();await browser.close();await new Promise(resolve=>server.close(resolve));}
