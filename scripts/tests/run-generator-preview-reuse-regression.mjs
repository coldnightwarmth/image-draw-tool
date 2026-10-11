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
const page=await browser.newPage({viewport:{width:1440,height:900}});const errors=[];page.on('pageerror',e=>errors.push(e.message));
const baseline=Boolean(process.env.GENERATOR_BASELINE_FILE);
await page.addInitScript(()=>{
 const nativeGetAnimations=Element.prototype.getAnimations;
 window.animationQueries=0;Element.prototype.getAnimations=function(...args){window.animationQueries++;return nativeGetAnimations.apply(this,args);};
 const NativeWorker=Worker;window.workerStats={created:0,prepares:0,frames:0,pending:0,maxPending:0};
 window.Worker=class extends NativeWorker{
  constructor(...args){super(...args);workerStats.created++;this.pending=new Set();this.addEventListener('message',({data})=>{if((data.type==='rendered'||data.type==='error')&&this.pending.delete(data.requestId)){workerStats.pending--;if(data.type==='rendered')workerStats.frames++;}});}
  postMessage(msg,...rest){if(msg.type==='prepare')workerStats.prepares++;if(msg.type==='render-frame'){this.pending.add(msg.requestId);workerStats.pending++;workerStats.maxPending=Math.max(workerStats.maxPending,workerStats.pending);}if(msg.type==='render-frame'&&window.holdNextRaster){window.holdNextRaster=false;window.releaseRaster=()=>super.postMessage(msg,...rest);return;}return super.postMessage(msg,...rest);}
  terminate(){workerStats.pending-=this.pending.size;this.pending.clear();return super.terminate();}
 };
});
await page.route('**/generator.js?*',async route=>{
 const response=await route.fetch();let source=baseline?await readFile(process.env.GENERATOR_BASELINE_FILE,'utf8'):await response.text();

 await route.fulfill({response,body:source.replace('  window.GeneratorApp = {','  window.testGenerator = {state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate, runGeneratorPixelatePreviews, startStablePreview, stopStablePreview, setSequencePaused, getStablePreview:()=>stablePreview, createCompositionThumbnailBlob};\n  window.GeneratorApp = {')});
});
try {
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 console.log('fixture start');
 await page.evaluate(async()=>{
  const record={controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()};
  const canvas=document.createElement('canvas');canvas.width=32;canvas.height=32;const ctx=canvas.getContext('2d');
  ctx.fillStyle='#e78435';ctx.fillRect(0,0,16,32);ctx.fillStyle='#326baf';ctx.fillRect(16,0,16,32);
  const source='upload:'+'c'.repeat(64);
  record.composition.uploadedAssets=[{source,dataUrl:canvas.toDataURL(),width:32,height:32,name:'fixture.png',folderId:'upload',folderName:'uploads',tags:[]}];
  record.controls.ranges.generatorOpacityRandomMinSlider='20';record.controls.ranges.generatorOpacityRandomMaxSlider='100';record.controls.ranges.generatorSizeRandomMinSlider='60';record.controls.ranges.generatorSizeRandomMaxSlider='80';record.controls.width='800';record.controls.height='600';record.controls.ranges.generatorCountSlider='300';record.controls.ranges.generatorMarkCountSlider='100';record.controls.smoothRenderPreview=false;record.controls.sequencePaused=false;record.controls.marginMode='placement';
  record.composition.settings={...record.composition.settings,width:800,height:600,margin:0,marginMode:'placement',count:300,markCount:100};
  const base=record.composition.specs[0];
  record.composition.specs=Array.from({length:300},(_,i)=>({...base,source,index:i,motifId:Math.floor(i/3),mode:'scatter',x:30+i%20*38,y:30+Math.floor(i/20)*38,width:64,height:64,longestSide:64,rotation:0,filter:'',tintAmount:0,opacity:.7,hidden:false,uncropped:false,
   markTransform:{a:1,b:0,c:0,d:1,pitch:0,yaw:0,horizontalStretch:100,verticalStretch:100},
   sequence:{effect:'pixelate',timing:'all',duration:2000,delay:0,moveX:0,moveY:0,rotationAmount:0,scaleAmount:1,filterRest:'none',filterActive:'contrast(2) saturate(0.6)',pixelateAmount:12,contrastAmount:2,pixelSaturation:.6},suspendedSequence:null}));
  await testGenerator.restoreCompositionRecord(record);
  await Promise.all([...document.querySelectorAll('img.generator-stamp')].map(i=>i.decode()));
  testGenerator.setSequencePaused(true);testGenerator.state.currentControlState=testGenerator.captureControlState();
  for(const img of document.querySelectorAll('img.generator-stamp'))for(const a of img.getAnimations())a.currentTime=800;
 });
 console.log('fixture ready');
 const pixelation=await page.evaluate(()=>{
  const times=[];window.animationQueries=0;
  for(let i=0;i<6;i++){
   cancelAnimationFrame(testGenerator.state.pixelatePreviewFrameId);testGenerator.state.pixelatePreviewFrameId=null;
   const start=performance.now();testGenerator.runGeneratorPixelatePreviews(100000+i*60);times.push(performance.now()-start);
  }
  cancelAnimationFrame(testGenerator.state.pixelatePreviewFrameId);testGenerator.state.pixelatePreviewFrameId=null;
  times.sort((a,b)=>a-b);
  const proxy=document.querySelector('.generator-pixelate-proxy');
  return {queries:animationQueries,medianMs:times[3],p95Ms:times[5],pixel:Array.from(proxy.getContext('2d').getImageData(0,0,1,1).data),filter:proxy.style.filter,transform:proxy.style.transform};
 });
 await page.locator('#generatorComposition').screenshot({path:baseline?'/tmp/generator-pixelation-before.png':'/tmp/generator-pixelation-after.png'});
 // Observe a scoped opacity edit: only related attributes should be written.
 const edit=async(value)=>page.evaluate(async value=>{
  let mutations=0;const observer=new MutationObserver(records=>mutations+=records.length);observer.observe(document.querySelector('#generatorComposition'),{attributes:true,subtree:true});
  const input=document.querySelector('#generatorOpacityRandomMinSlider');input.value=String(value);input.dispatchEvent(new Event('input',{bubbles:true}));
  const started=performance.now();await Promise.race([testGenerator.applyPendingDynamicUpdate(),new Promise((_,reject)=>setTimeout(()=>reject(new Error('Edit timed out '+JSON.stringify({stats:workerStats,generating:testGenerator.state.generating,pending:!!testGenerator.state.dynamicUpdateBase}))),15000))]);await Promise.resolve();observer.disconnect();return{mutations,ms:performance.now()-started};
 },value);
 console.log('pixelation measured',pixelation);
 const nativeEdit=await edit(31);console.log('native edit',nativeEdit);
 assert.equal(await page.evaluate(()=>testGenerator.state.currentCount),300);
 // Use real animated sources for repeated smooth-preview edits and decoding cost.
 await page.evaluate(async()=>{
  const record={controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()};
  const sources=testGenerator.state.catalog.filter(b=>!b.dataUrl&&b.width<=128&&b.height<=128).slice(0,30);
  record.composition.specs.forEach((s,i)=>{s.source=sources[i%sources.length].source;s.sequence=null;});
  record.controls.sequenceEnabled=false;record.controls.smoothRenderPreview=true;
  await testGenerator.restoreCompositionRecord(record);
 });
 await page.waitForFunction(()=>GeneratorApp.getSummary().previewFrames>=2,null,{timeout:120000});
 console.log('smooth ready');
 const before=await page.evaluate(()=>({...workerStats}));
 const smoothEdits=[];
 for(const value of [32,33,34]){
  const frames=await page.evaluate(()=>workerStats.frames);const started=Date.now();
  console.log('edit begin',value);
  await edit(value);console.log('edit done',value);
  assert.equal(await page.evaluate(()=>testGenerator.state.currentCount),300);
  await page.waitForFunction(frames=>workerStats.frames>frames+1,frames,{timeout:120000});
  smoothEdits.push(Date.now()-started);console.log('smooth edit',value,smoothEdits.at(-1));
 }
 const after=await page.evaluate(()=>({...workerStats}));
 if(!baseline){assert.equal(after.prepares,before.prepares,'property edits reuse decoded GIFs');assert.equal(after.created,before.created,'property edits reuse worker');assert(pixelation.queries<=300);assert(nativeEdit.mutations<=1000);}
 assert.equal(after.maxPending,1,'only one frame in flight');
 if(!baseline){
  // A delayed old frame must never unblock a thumbnail of an edited scene.
  await page.evaluate(()=>{window.holdNextRaster=true;testGenerator.getStablePreview().wake();});
  await page.waitForFunction(()=>typeof window.releaseRaster==='function');
  await page.evaluate(async()=>{
   testGenerator.state.currentSpecs[0].opacity=.25;await testGenerator.startStablePreview();
   testGenerator.state.currentSpecs[0].opacity=.5;await testGenerator.startStablePreview();
   window.thumbnailReady=false;window.thumbnail=testGenerator.createCompositionThumbnailBlob().then(()=>{window.thumbnailReady=true;});
  });
  await page.waitForTimeout(100);assert.equal(await page.evaluate(()=>thumbnailReady),false);
  await page.evaluate(()=>{releaseRaster();delete window.releaseRaster;});
  await page.waitForFunction(()=>thumbnailReady);
  assert.equal(await page.evaluate(()=>workerStats.maxPending),1);
  assert.equal(await page.evaluate(()=>testGenerator.getStablePreview().readyResolvers.length),0);
  // Entry-derived scale/sampling are part of decoding preparation, even when
  // the declared asset descriptors do not change.
  for(const effect of ['scale','pixelate']){
   const previous=await page.evaluate(()=>workerStats.prepares);
   await page.evaluate(async effect=>{
    testGenerator.state.currentSpecs[0].sequence={effect,timing:'all',duration:2000,delay:-1000,moveX:0,moveY:0,rotationAmount:0,scaleAmount:2,pixelateAmount:12};
    await testGenerator.startStablePreview();
   },effect);
   assert.equal(await page.evaluate(()=>workerStats.prepares),previous+1);
  }
 }

 // Size increases must rebuild at the requested resolution, never reuse undersized decoding.
 const prepares=await page.evaluate(()=>workerStats.prepares);
 await page.evaluate(async()=>{const input=document.querySelector('#generatorSizeRandomMaxSlider');input.value=180;input.dispatchEvent(new Event('input',{bubbles:true}));await testGenerator.applyPendingDynamicUpdate();});
 await page.waitForFunction(n=>workerStats.prepares>n,prepares);
 await page.waitForFunction(()=>GeneratorApp.getSummary().previewFrames>=2,null,{timeout:120000});
 await page.locator('#generatorCropInspectButton').click({force:true});
 assert.equal(await page.evaluate(()=>GeneratorApp.getSummary().previewRenderer),'dom');
 await page.locator('#generatorCropInspectButton').click({force:true});
 await page.waitForFunction(()=>GeneratorApp.getSummary().previewFrames>=2,null,{timeout:120000});
 await page.locator('#generatorSmoothPreviewToggle').uncheck({force:true});
 assert.equal(await page.evaluate(()=>GeneratorApp.getSummary().previewRenderer),'dom');
 assert.deepEqual(errors,[]);
 console.log(JSON.stringify({baseline,pixelation,nativeEdit,smoothEditMs:smoothEdits,extraWorkers:after.created-before.created,extraPrepares:after.prepares-before.prepares},null,2));
 console.log('PASS native pixelation, scoped DOM updates, smooth-preview reuse, resolution changes, inspection and native restoration');
}finally{await browser.close();await new Promise(r=>server.close(r));}
