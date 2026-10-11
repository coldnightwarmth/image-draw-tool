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
const baseline=Boolean(process.env.GENERATOR_BASELINE_FILE);
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();const source=baseline?await readFile(process.env.GENERATOR_BASELINE_FILE,'utf8'):await response.text();await route.fulfill({response,body:source.replace('  window.GeneratorApp = {','  window.testGenerator = {state, setCropInspectionActive, captureControlState, captureCurrentComposition, restoreCompositionRecord};\n  window.GeneratorApp = {')});});
try{
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 await page.evaluate(async()=>{
  const record={controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()};
  const canvas=document.createElement('canvas');canvas.width=256;canvas.height=256;const ctx=canvas.getContext('2d');
  const pixels=ctx.createImageData(256,256);let seed=42;for(let i=0;i<pixels.data.length;i+=4){seed=(Math.imul(seed,1664525)+1013904223)>>>0;pixels.data[i]=seed>>>24;pixels.data[i+1]=seed>>>16;pixels.data[i+2]=seed>>>8;pixels.data[i+3]=255;}ctx.putImageData(pixels,0,0);
  const source='upload:'+'d'.repeat(64);window.fixtureSource=canvas.toDataURL();
  record.composition.uploadedAssets=[{source,dataUrl:fixtureSource,width:256,height:256,name:'fixture.png',folderId:'upload',folderName:'uploads',tags:[]}];
  record.controls.smoothRenderPreview=false;record.controls.sequenceEnabled=false;
  const base=record.composition.specs[0];record.composition.specs=Array.from({length:300},(_,i)=>({...base,source,index:i,motifId:Math.floor(i/3),x:100+i%20*20,y:100+Math.floor(i/20)*20,width:48,height:48,hidden:false,uncropped:false,sequence:null,suspendedSequence:null,filter:'',opacity:1}));
  await testGenerator.restoreCompositionRecord(record);
  await Promise.all([...document.querySelectorAll('img.generator-stamp')].map(image=>image.decode()));
  window.snapshotUrls=new Set();window.snapshotCreated=0;
  const create=URL.createObjectURL.bind(URL),revoke=URL.revokeObjectURL.bind(URL);
  URL.createObjectURL=blob=>{const url=create(blob);snapshotUrls.add(url);snapshotCreated++;return url;};
  URL.revokeObjectURL=url=>{snapshotUrls.delete(url);return revoke(url);};
 });
 const started=Date.now();
 const blockingMs=await page.evaluate(()=>{const started=performance.now();testGenerator.setCropInspectionActive(true,'sample');return performance.now()-started;});
 await page.waitForFunction(()=>[...document.querySelectorAll('img.generator-stamp')].every(i=>i.dataset.cropInspectionPausedSrc&&i.complete));
 if(!baseline)await page.waitForFunction(()=>document.querySelector('#generatorCropInspectButton').getAttribute('aria-busy')==='false');
 const readyMs=Date.now()-started;
 const parity=await page.evaluate(async()=>{
  const original=new Image();original.src=fixtureSource;await original.decode();
  const a=document.createElement('canvas');a.width=a.height=256;const ctx=a.getContext('2d',{willReadFrequently:true});ctx.drawImage(original,0,0);const before=ctx.getImageData(0,0,256,256).data;
  ctx.clearRect(0,0,256,256);ctx.drawImage(document.querySelector('img.generator-stamp'),0,0);const after=ctx.getImageData(0,0,256,256).data;return before.every((v,i)=>v===after[i]);
 });assert(parity);
 if(baseline){console.log(JSON.stringify({baseline,blockingMs,readyMs}));}
 else{
  await page.keyboard.press('Escape');
  assert.equal(await page.evaluate(()=>testGenerator.state.cropInspectionActive),false);
  assert.equal(await page.evaluate(()=>snapshotUrls.size),0);
  // Artificially delay encoding callbacks to reliably exercise the 750ms spinner.
  await page.evaluate(()=>{
   const native=HTMLCanvasElement.prototype.toBlob;
   HTMLCanvasElement.prototype.toBlob=function(callback,...rest){return native.call(this,blob=>setTimeout(()=>callback(blob),1100),...rest);};
   window.beforeCancellationSources=[...document.querySelectorAll('img.generator-stamp')].map(i=>i.src);
  });
  await page.locator('#generatorMarkInspectButton').click();
  await page.waitForTimeout(400);
  assert.equal(await page.locator('#generatorMarkInspectButton').evaluate(e=>e.classList.contains('is-inspection-loading')),false);
  await page.waitForFunction(()=>document.querySelector('#generatorMarkInspectButton').classList.contains('is-inspection-loading'));
  // Switching mode transfers the loading indicator without restarting the job.
  await page.locator('#generatorCropInspectButton').click();
  assert.equal(await page.locator('#generatorCropInspectButton').evaluate(e=>e.classList.contains('is-inspection-loading')),true);
  await page.keyboard.press('Escape');
  assert.equal(await page.evaluate(()=>testGenerator.state.cropInspectionActive),false);
  assert.equal(await page.locator('.is-inspection-loading').count(),0);
  await page.waitForTimeout(1300);
  assert.equal(await page.evaluate(()=>snapshotUrls.size),0);
  assert.equal(await page.evaluate(()=>[...document.querySelectorAll('img.generator-stamp')].every((i,n)=>!i.dataset.cropInspectionPausedSrc&&i.src===beforeCancellationSources[n])),true);
  // Re-enter and cancel immediately, before the first scheduled snapshot.
  await page.evaluate(()=>{testGenerator.setCropInspectionActive(true,'mark');document.dispatchEvent(new KeyboardEvent('keydown',{key:'Escape',bubbles:true}));});
  await page.waitForTimeout(50);assert.equal(await page.locator('.is-inspection-loading').count(),0);
  assert.equal(await page.evaluate(()=>testGenerator.state.cropInspectionActive),false);
  console.log(JSON.stringify({baseline,blockingMs,readyMs}));
  console.log('PASS 300-sample startup, lossless stills, 750ms spinner, mode switch, Escape during/completed loading, and URL cleanup');
 }
 assert.deepEqual(errors,[]);
}finally{await browser.close();await new Promise(r=>server.close(r));}
