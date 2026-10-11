import assert from 'node:assert/strict';
import {chromium} from 'playwright';
import {createServer} from 'node:http';
import {readFile} from 'node:fs/promises';
import {resolve,extname} from 'node:path';
import {fileURLToPath} from 'node:url';
const root=fileURLToPath(new URL('../../',import.meta.url));
const server=createServer(async(req,res)=>{try{let path=decodeURIComponent(new URL(req.url,'http://localhost').pathname);if(path.endsWith('/'))path+='index.html';path=resolve(root,'.'+path);if(!path.startsWith(root))throw Error();const data=await readFile(path);res.writeHead(200,{'Content-Type':({'.js':'text/javascript','.mjs':'text/javascript','.html':'text/html','.css':'text/css','.gif':'image/gif','.wasm':'application/wasm'})[extname(path)]||'application/octet-stream'});res.end(data);}catch{res.writeHead(404);res.end();}});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const browser=await chromium.launch({headless:true,...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH?{executablePath:process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH}:{})});
const page=await browser.newPage();const errors=[];page.on('pageerror',e=>errors.push(e.message));
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {createGeneratorExportEntry, randomizeGenerationControls, buildSequenceAssignments, readSettings, state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};
try {
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 const workerSource=await readFile(resolve(root,'export-raster-worker.js'),'utf8');
 const renderer=workerSource.slice(workerSource.indexOf('function createTintedSource('),workerSource.indexOf('// For fixed, tinted collage entries'));
 const result=await page.evaluate(renderer=>{
  const render=new Function('ensureScratch','applyColorMatrix','applyPixelation',renderer+';return createTintedSource;')(
   ()=>{const canvas=new OffscreenCanvas(8,8);return {canvas,context:canvas.getContext('2d')};},()=>{},()=>{});
  const source=new OffscreenCanvas(8,8),ctx=source.getContext('2d');
  ctx.fillStyle='#e78435';ctx.fillRect(0,0,4,8);ctx.fillStyle='#326baf';ctx.fillRect(4,0,4,8);
  const base={...testGenerator.state.currentSpecs[0],filter:'sepia(0.4) saturate(3) hue-rotate(120deg)',sequence:null};
  const plan={sequenceRates:new Map(),sourceRates:new Map()};
  const outputs=[];
  for(const effect of [null,'color-cycle','pixelate']) {
   const spec={...base,sequence:effect?{effect,duration:1000,delay:0,timing:'step',hueAmount:130,activeSaturation:2.7,contrastAmount:2.5,pixelSaturation:.6,pixelateAmount:1}:null};
   const entry=testGenerator.createGeneratorExportEntry(spec,500,plan);
   const expected=base.filter+(effect==='color-cycle'?' hue-rotate(130deg) saturate(2.7)':effect==='pixelate'?' contrast(2.5) saturate(0.6)':'');
   const canvas=new OffscreenCanvas(8,8),context=canvas.getContext('2d');context.filter=expected;context.drawImage(source,0,0);
   const actual=render({},source,8,8,{...entry,tintLayers:[]}).context.getImageData(0,0,8,8).data;
   const wanted=context.getImageData(0,0,8,8).data;
   outputs.push({effect,filter:entry.colorFilter,maxError:Math.max(...actual.map((v,i)=>Math.abs(v-wanted[i])))});
  }
  return outputs;
 },renderer);
 for(const row of result) assert.equal(row.maxError,0,JSON.stringify(row));
 assert.equal(errors.length,0,errors.join('\n'));console.log('PASS export color filter pixel parity',result);
} finally {await browser.close();await new Promise(r=>server.close(r));}
