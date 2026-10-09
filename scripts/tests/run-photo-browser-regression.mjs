#!/usr/bin/env node
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { readFile, mkdir, writeFile } from 'node:fs/promises';
import { extname, resolve, sep } from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright';
import { resolveRasterMemoryBudget, PHOTO_EXPORT_MEMORY_PROFILE, MAX_PHOTO_EXPORT_MEMORY_BYTES } from '../../raster-memory-budget.mjs';
const root = fileURLToPath(new URL('../../', import.meta.url));
const mime={'.html':'text/html','.js':'text/javascript','.mjs':'text/javascript','.css':'text/css','.gif':'image/gif','.webp':'image/webp','.json':'application/json','.wasm':'application/wasm'};
const server=createServer(async(req,res)=>{
 try {
  let url=decodeURIComponent(new URL(req.url,'http://localhost').pathname); if(url.endsWith('/'))url+='index.html';
  const path=resolve(root,`.${url}`); if(!path.startsWith(resolve(root)+sep))throw Error('Invalid path');
  res.writeHead(200,{'Content-Type':mime[extname(path)]||'application/octet-stream'}); res.end(await readFile(path));
 }catch{res.writeHead(404);res.end();}
});
await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
const browser=await chromium.launch({headless:true,...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH?{executablePath:process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH}:{})});
const context=await browser.newContext({viewport:{width:1280,height:900},acceptDownloads:true});
const page=await context.newPage();page.setDefaultTimeout(30000);
const errors=[];page.on('pageerror',error=>errors.push(error.message));
const artifacts=process.env.PHOTO_TEST_ARTIFACTS;
if(artifacts)await mkdir(artifacts,{recursive:true});
const gif=Buffer.from('R0lGODlhGAAYAIEAAOYeKAAAAAAAAAAAACH/C05FVFNDQVBFMi4wAwEAAAAh+QQACgAAACwAAAAAGAAYAAAIKQABCBxIsKDBgwgTKlzIsKHDhxAjSpxIsaLFixgzatzIsaPHjyBDPgwIACH5BAEUAAEALAAAAAAYABgAgR4e5gAAAAAAAAAAAAgpAAEIHEiwoMGDCBMqXMiwocOHECNKnEixosWLGDNq3Mixo8ePIEM+DAgAOw==','base64');
const summary=()=>page.evaluate(()=>PhotoApp.getSummary());
const settled=async()=>{await page.waitForFunction(()=>!PhotoApp.getSummary().fitting&&PhotoApp.getSummary().previewReady,{},{timeout:120000});};
const change=async(id,value)=>{await page.locator(id).evaluate((element,value)=>{element.value=String(value);element.dispatchEvent(new Event('input',{bubbles:true}));},value);};
try {
 await page.goto(`http://127.0.0.1:${server.address().port}/photo/`);
 await page.waitForFunction(()=>PhotoApp?.getSummary().ready);
 assert((await summary()).assets>3000);
 const images=await page.evaluate(async()=>{
  const c=document.createElement('canvas');c.width=96;c.height=80;const ctx=c.getContext('2d');
  ctx.fillStyle='#201536';ctx.fillRect(0,0,96,80);ctx.fillStyle='#e61e28';ctx.fillRect(0,0,48,80);ctx.fillStyle='#26c15a';ctx.fillRect(48,40,48,40);
  const target=c.toDataURL().split(',')[1];ctx.clearRect(0,0,96,80);ctx.fillStyle='#26c15a';ctx.fillRect(8,8,80,64);
  return {target,asset:c.toDataURL().split(',')[1]};
 });
 await page.locator('#sourceMode button[value=local]').click();
 await page.locator('#assetsInput').setInputFiles([
  {name:'timing.gif',mimeType:'image/gif',buffer:gif},
  {name:'transparent.png',mimeType:'image/png',buffer:Buffer.from(images.asset,'base64')},
  {name:'broken.gif',mimeType:'image/gif',buffer:Buffer.from('GIF89a bad image')}
 ]);
 await page.waitForFunction(()=>!PhotoApp.getSummary().importing&&PhotoApp.getSummary().localAssets===2);
 assert.match(await page.locator('#localStatus').textContent(),/1 unreadable/);
 await page.locator('#animatePreview').uncheck();
 await page.locator('#referenceInput').setInputFiles({name:'test-target.png',mimeType:'image/png',buffer:Buffer.from(images.target,'base64')});
 await settled();
 const baseline=await summary();assert(baseline.count>0);assert(baseline.error<baseline.baseError*.3);
 const original=await page.evaluate(()=>PhotoApp.getComposition());
 // The output only references local assets, never a hidden reference-image layer.
 assert(original.entries.every(e=>e.assetId.startsWith('local:')));
 await page.locator('#refineButton').click();await settled();
 assert((await summary()).count>=baseline.count);
 await page.locator('#showReference').check();assert(await page.locator('#photoOriginal').isVisible());await page.locator('#showReference').uncheck();
 // Native GIF frame timing is preserved by the shared worker (100 + 200 ms).
 const timing=await page.evaluate(async()=>{
  const {RasterSession,createScene}=await import('/photo/raster-client.mjs');
  const bytes=Uint8Array.from(atob('R0lGODlhGAAYAIEAAOYeKAAAAAAAAAAAACH/C05FVFNDQVBFMi4wAwEAAAAh+QQACgAAACwAAAAAGAAYAAAIKQABCBxIsKDBgwgTKlzIsKHDhxAjSpxIsaLFixgzatzIsaPHjyBDPgwIACH5BAEUAAEALAAAAAAYABgAgR4e5gAAAAAAAAAAAAgpAAEIHEiwoMGDCBMqXMiwocOHECNKnEixosWLGDNq3Mixo8ePIEM+DAgAOw=='),c=>c.charCodeAt(0));
  const url=URL.createObjectURL(new Blob([bytes],{type:'image/gif'}));const session=new RasterSession();
  try{
   const composition={background:[10,20,30],referenceWidth:32,referenceHeight:32,entries:[{assetId:'a',x:.5,y:.5,size:.75,rotation:0,opacity:1,tintAmount:0,tint:[0,0,0],phase:0}]};
   const catalog=new Map([['a',{url,width:24,height:24,frames:2,source:'a.gif'}]]);
   const prepared=await session.prepare(createScene(composition,catalog,32,32));
   const out=[];for(const time of [0,99,100,299,300]){const frame=await session.frame(time,'rgba');const p=new Uint8Array(frame.buffer);out.push({center:Array.from(p.slice((16*32+16)*4,(16*32+16)*4+4)),corner:Array.from(p.slice(0,4))});}
   return {frames:out,durations:prepared.assets[0].durations,memory:prepared.memory,deviceMemoryGiB:navigator.deviceMemory};
  }finally{session.close();URL.revokeObjectURL(url);}
 });
 assert.deepEqual(timing.durations,[100,200]);
 assert.deepEqual(timing.frames.map(f=>f.center),[[230,30,40,255],[230,30,40,255],[30,30,230,255],[30,30,230,255],[230,30,40,255]]);
 assert.deepEqual(timing.frames[0].corner,[10,20,30,255],'background reaches the renderer without a color conversion mismatch');
 assert.equal(timing.memory.budgetBytes,resolveRasterMemoryBudget(MAX_PHOTO_EXPORT_MEMORY_BYTES,{deviceMemoryGiB:timing.deviceMemoryGiB,profile:PHOTO_EXPORT_MEMORY_PROFILE}),'the actual worker accepts the photo export allowance');
 const legacyBudget=await page.evaluate(async()=>{
  const {RasterSession}=await import('/photo/raster-client.mjs');const session=new RasterSession();
  try {return (await session.prepare({quality:false,memoryProfile:'photo-export',memoryBudgetBytes:2048*1024*1024,outputWidth:2,outputHeight:2,entries:[],assets:[]})).memory.budgetBytes;}
  finally{session.close();}
 });
 assert.equal(legacyBudget,resolveRasterMemoryBudget(MAX_PHOTO_EXPORT_MEMORY_BYTES,{deviceMemoryGiB:timing.deviceMemoryGiB}),'preview cannot opt into export-only memory');
 // Exact-frame reuse must preserve effects, order, phase, and alpha even when
 // a deliberately small budget evicts copies between repeated source uses.
 const cacheParity=await page.evaluate(async()=>{
  const {RasterSession}=await import('/photo/raster-client.mjs');
  const small=Uint8Array.from(atob('R0lGODlhGAAYAIEAAOYeKAAAAAAAAAAAACH/C05FVFNDQVBFMi4wAwEAAAAh+QQACgAAACwAAAAAGAAYAAAIKQABCBxIsKDBgwgTKlzIsKHDhxAjSpxIsaLFixgzatzIsaPHjyBDPgwIACH5BAEUAAEALAAAAAAYABgAgR4e5gAAAAAAAAAAAAgpAAEIHEiwoMGDCBMqXMiwocOHECNKnEixosWLGDNq3Mixo8ePIEM+DAgAOw=='),c=>c.charCodeAt(0));
  small[6]=small[8]=0;small[7]=small[9]=2; // 512-square logical canvas; tiny delta patches.
  const assets=Array.from({length:32},(_,id)=>({id:String(id),kind:'gif',bytes:small}));
  const entries=Array.from({length:160},(_,index)=>({sourceId:String(index%32),centerX:index%8*8+4,centerY:Math.floor(index/8)%8*8+4,width:12,height:11,rotation:index%37,opacity:.6,imageRendering:'auto',phaseOffsetMs:index%32*10,tintLayers:[{color:'#12683a',amountPercent:index%50}]}));
  const outputs=[];
  for(const cacheRepeatedSources of [false,true]) {
   const session=new RasterSession();const samples=[];
   try {
    await session.prepare({quality:true,cacheRepeatedSources,memoryBudgetBytes:64*1024*1024,outputWidth:64,outputHeight:64,selectionBounds:{left:0,top:0,right:64,bottom:64},background:{include:true,color:'#123456'},assets,entries});
    for(const time of [0,100,240,300,0]) samples.push(Array.from(new Uint8Array((await session.frame(time,'rgba')).buffer)));
   }finally{session.close();}
   outputs.push(samples);
  }
  return outputs[0].every((frame,index)=>frame.every((value,offset)=>value===outputs[1][index][offset]));
 });
 assert(cacheParity,'bounded source copies preserve exact full-quality output');
 // Grid controls and cancellation are exercised through the actual sidebar.
 await change('#photo-count',100);await page.locator('#gridMode').check();await page.waitForTimeout(350);await settled();
 const grid=await page.evaluate(()=>PhotoApp.getComposition());assert(grid.entries.every(e=>e.rotation===0));
 assert(await page.locator('#photo-rotation').isDisabled());
 await page.locator('#gridMode').uncheck();await change('#photo-count',8000);
 await page.waitForFunction(()=>PhotoApp.getSummary().fitting);
 await page.locator('#stopButton').click();
 assert.equal((await summary()).fitting,false);
 await change('#photo-count',100);await change('#photo-recolor',0);await page.waitForTimeout(350);await settled();
 const exports=await page.evaluate(async()=>{
  window.photoExports={};const result=[];
  for(const format of ['png','webp','mp4']) {
   const output=await PhotoApp.export({format,width:128,seconds:1,timeMs:0,download:false});
   window.photoExports[format]=output.blob;const {blob,...metadata}=output;result.push({...metadata,bytes:blob.size,type:blob.type});
  }
  return result;
 });
 assert(exports.every(e=>e.bytes>100));assert.equal(exports[1].frameCount,50);assert.equal(exports[2].frameCount,60);
 console.log('exports',exports);
 const fidelity=await page.evaluate(async()=>{
  const png=await createImageBitmap(photoExports.png);
  const decoder=new ImageDecoder({data:await photoExports.webp.arrayBuffer(),type:'image/webp'});await decoder.tracks.ready;
  const first=await decoder.decode({frameIndex:0}),second=await decoder.decode({frameIndex:6});
  const canvas=new OffscreenCanvas(png.width,png.height),ctx=canvas.getContext('2d',{willReadFrequently:true});
  const read=source=>{ctx.drawImage(source,0,0);return ctx.getImageData(0,0,png.width,png.height).data;};
  const a=read(png),b=read(first.image),c=read(second.image);
  let changed=0,drift=0;for(let i=0;i<a.length;i++){if(b[i]!==c[i])changed++;if(a[i]!==b[i])drift++;}
  const frames=decoder.tracks.selectedTrack.frameCount;png.close();first.image.close();second.image.close();decoder.close();
  const url=URL.createObjectURL(photoExports.mp4),video=document.createElement('video');video.muted=true;video.src=url;document.body.append(video);
  const loaded=new Promise((resolve,reject)=>{video.onloadeddata=resolve;video.onerror=()=>reject(Error('MP4 could not be played'));});await loaded;
  const samples=[];for(const time of [.02,.16,.4,.92]){
   await new Promise(resolve=>{video.onseeked=resolve;video.currentTime=time;});
   ctx.drawImage(video,0,0,canvas.width,canvas.height);const rgba=ctx.getImageData(0,0,canvas.width,canvas.height).data;let sum=0;for(let i=0;i<rgba.length;i+=4)sum+=rgba[i];samples.push(sum);
  }
  const duration=video.duration;video.remove();video.src='';URL.revokeObjectURL(url);
  return {drift,changed,frames,duration,samples};
 });
 assert.equal(fidelity.drift,0,'WebP frame pixels equal lossless PNG');assert(fidelity.changed>100,'WebP animates');assert.equal(fidelity.frames,50);
 assert(Math.abs(fidelity.duration-1)<.04,'MP4 has the requested duration');assert(new Set(fidelity.samples).size>1,'MP4 seeks to changing frames');
 console.log('fidelity',fidelity);
 if(artifacts)for(const format of ['png','webp','mp4'])await writeFile(resolve(artifacts,`fixture.${format}`),Buffer.from(await page.evaluate(async format=>Array.from(new Uint8Array(await photoExports[format].arrayBuffer())),format)));
 await page.locator('#exportButton').click();
 await change('#exportDuration',15);
 const exportPromise=page.evaluate(()=>PhotoApp.export({format:'mp4',width:128,seconds:15,download:false}).then(()=>false,error=>error.name==='AbortError'));
 await page.waitForFunction(()=>PhotoApp.getSummary().exporting);await page.locator('#cancelExport').click();assert.equal(await exportPromise,true);
 await page.locator('#closeExport').click();await settled();
 // Make sure the download button produces an actual file, not just an in-memory result.
 await page.locator('#exportButton').click();await page.locator('#exportFormat button[value=png]').click();
 const downloadPromise=page.waitForEvent('download');await page.locator('#startExport').click();const download=await downloadPromise;
 assert(download.suggestedFilename().endsWith('.png'));await page.waitForFunction(()=>!PhotoApp.getSummary().exporting);await page.locator('#closeExport').click();
 // An isolated browser filesystem exercises chosen-folder writes/collisions
 // without asking for access to or touching any real user download folder.
 await page.evaluate(async()=>{window.photoTestFolder=await navigator.storage.getDirectory();window.showDirectoryPicker=async()=>photoTestFolder;});
 await page.locator('#exportButton').click();await page.locator('#chooseExportFolder').click();
 for(let index=0;index<2;index++) {await page.locator('#startExport').click();await page.waitForFunction(()=>!PhotoApp.getSummary().exporting&&document.querySelector('#exportStatus').textContent==='saved');}
 const files=await page.evaluate(async()=>{const files=[];for await(const [name,handle] of photoTestFolder.entries())files.push({name,size:(await handle.getFile()).size});return files;});
 assert.equal(files.length,2);assert(files.every(file=>file.size>100));assert(files.some(file=>file.name.endsWith('-1.png')));
 await page.locator('#closeExport').click();
 await page.evaluate(()=>window.dispatchEvent(new PageTransitionEvent('pagehide',{persisted:true})));
 assert.equal((await summary()).previewReady,false);
 await page.evaluate(()=>window.dispatchEvent(new PageTransitionEvent('pageshow',{persisted:true})));await settled();
 // Cancelling a completed-but-unaccepted import retains the previous folder.
 const importRace=await page.evaluate(async()=>{
  const worker=new Worker('/photo/match-worker.js',{type:'module'});
  const canvas=new OffscreenCanvas(16,16),ctx=canvas.getContext('2d');ctx.fillStyle='#123456';ctx.fillRect(0,0,16,16);
  const file=new File([await canvas.convertToBlob()], 'sample.png',{type:'image/png'});
  const source=URL.createObjectURL(file);
  const request=(message,expected)=>new Promise((resolve,reject)=>{
   const receive=({data})=>{if(data.id===message.id&&(data.type===expected||data.type==='error')){worker.removeEventListener('message',receive);data.type==='error'?reject(Error(data.message)):resolve(data);}};
   worker.addEventListener('message',receive);worker.postMessage(message);
  });
  try{
   await request({type:'import',id:1,items:[{id:'old',source,file}]},'imported');worker.postMessage({type:'commit-import',id:1});
   await request({type:'import',id:2,items:[{id:'new',source,file}]},'imported');worker.postMessage({type:'cancel'});
   const pixels=new Uint8ClampedArray(32*32*4).fill(255);
   const result=await request({type:'fit',id:3,width:32,height:32,pixels,sourceMode:'local',settings:{grid:true,count:25},seed:1},'fitted');
   result.bitmap.close();return result.entries.length>0&&result.entries.every(entry=>entry.assetId==='old');
  }finally{worker.terminate();URL.revokeObjectURL(source);}
 });
 assert(importRace,'late import cancellation retains the previous asset set');
 const actionOrder=await page.locator('.workspace-actions button').evaluateAll(buttons=>buttons.map(button=>button.id));
 assert.deepEqual(actionOrder,['rerollButton','refineButton','playButton','exportButton']);
 await page.setViewportSize({width:390,height:844});await page.waitForTimeout(100);
 const layout=await page.evaluate(()=>({width:document.documentElement.scrollWidth,viewport:innerWidth,controls:document.querySelector('#controls').getBoundingClientRect().width}));
 assert(layout.width<=layout.viewport,'phone layout does not overflow horizontally');assert(layout.controls<=layout.viewport);
 if(artifacts)await page.screenshot({path:resolve(artifacts,'mobile.png'),fullPage:true});
 await page.setViewportSize({width:320,height:680});
 const actions=await page.locator('.workspace-actions button').evaluateAll(buttons=>buttons.map(button=>{const r=button.getBoundingClientRect();return {left:r.left,right:r.right,top:r.top,bottom:r.bottom,clipped:button.scrollWidth>button.clientWidth};}));
 assert(actions.every(rect=>rect.left>=0&&rect.right<=320&&rect.bottom<=680),'all four actions remain on screen on a narrow phone');
 assert(actions.every((rect,index)=>index===0||rect.left>=actions[index-1].right),'the action buttons do not overlap');
 assert(actions.every(rect=>!rect.clipped),'button labels fit without clipping');
 assert.deepEqual(errors,[]);
 console.log(JSON.stringify({passed:true,matching:baseline,layout}));
}finally{await browser.close();server.close();}
