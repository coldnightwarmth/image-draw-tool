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
  await page.route('**/generator.js?*', async route => {
    const response = await route.fetch();
    const source = (await response.text()).replace('  window.GeneratorApp = {',
      '  window.qualityTest = { state, getGeneratorQualityMp4EncoderConfig, createGeneratorExportScene, createGeneratorLoopPlan, createGeneratorRasterSession, renderGeneratorFramePixels };\n  window.GeneratorApp = {');
    await route.fulfill({ response, body: source });
  });
  await page.goto(url, {waitUntil:'load'});
  await page.waitForFunction(() => window.GeneratorApp?.getSummary().count === 120 && document.querySelector('#generatorCanvas').getAttribute('aria-busy') === 'false');
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
    state.currentBackground='#123456';state.currentCount=300;
    const base=state.currentSpecs[0];
    state.currentSpecs=Array.from({length:300},(_,i)=>({...base,index:i,motifId:i,x:16+(i%20)*16,y:10+Math.floor(i/20)*21,
      width:32,height:32,opacity:1,rotation:0,tintAmount:0,uncropped:i%15===0,markTransform:null,
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
  const fidelity = await page.evaluate(async () => {
    const {state, createGeneratorLoopPlan, createGeneratorExportScene, createGeneratorRasterSession, renderGeneratorFramePixels}=qualityTest;
    const specs=state.currentSpecs, background=state.currentBackground;
    const dimensions={width:state.currentWidth,height:state.currentHeight};
    const refs={};
    for(const quality of [false,true]) {
      const task={cancelled:false,quality};
      const session=createGeneratorRasterSession(task);
      try {
        let plan=createGeneratorLoopPlan(specs,null,1000);
        const prepared=await session.prepare(createGeneratorExportScene(specs,dimensions,background,plan,true,quality));
        plan=createGeneratorLoopPlan(specs,new Map(prepared.assets.map(a=>[a.id,a.totalDurationMs])),1000);
        refs[quality?'quality':'normal']=[];
        for(const time of [0,500]) refs[quality?'quality':'normal'].push(await renderGeneratorFramePixels(session,
          specs.filter(s=>!s.uncropped),specs.filter(s=>s.uncropped),time,plan,dimensions,background));
      } finally {session.release();}
    }
    const canvas=new OffscreenCanvas(320,320),ctx=canvas.getContext('2d',{willReadFrequently:true});
    const mse=(actual,expected)=>{
      let sum=0;for(let i=0;i<actual.length;i++)if(i%4!==3)sum+=(actual[i]-expected[i])**2;
      return sum/(actual.length*3/4);
    };
    const errors={};
    for(const mode of ['normal','quality']) {
      const video=document.createElement('video');video.muted=true;
      const url=URL.createObjectURL(exportFixtures[mode]);
      try {
        await new Promise((resolve,reject)=>{video.onloadeddata=resolve;video.onerror=()=>reject(Error('Invalid MP4'));video.src=url;});
        if(Math.abs(video.duration-1)>0.025)throw Error('Incorrect MP4 duration: '+video.duration);
        errors[mode]=[];
        for(const [i,time] of [0,0.5].entries()) {
          await new Promise((resolve,reject)=>{video.onseeked=resolve;video.onerror=reject;video.currentTime=time+0.001;});
          ctx.drawImage(video,0,0);errors[mode].push(mse(ctx.getImageData(0,0,320,320).data,refs[mode][i]));
        }
      } finally {video.removeAttribute('src');video.load();URL.revokeObjectURL(url);}
    }
    const decoder=new ImageDecoder({data:await exportFixtures.webp.arrayBuffer(),type:'image/webp'});
    try {
      for(const [i,frameIndex] of [0,25].entries()) {
        const {image}=await decoder.decode({frameIndex});ctx.drawImage(image,0,0);image.close();
        const error=mse(ctx.getImageData(0,0,320,320).data,refs.quality[i]);
        if(error!==0)throw Error('Lossless WebP pixel mismatch: '+error);
      }
    } finally {decoder.close();}
    return errors;
  });
  console.log('Decoded MP4 pixel MSE (lower is better):',JSON.stringify(fidelity));
  assert.ok(fidelity.quality.reduce((a,b)=>a+b,0)<fidelity.normal.reduce((a,b)=>a+b,0)*0.5,'quality MP4 should substantially reduce compression error');
  assert.ok(fidelity.quality.every(error=>error<20),'quality frames should remain faithful to the raster');
  // Three adjacent choices remain usable at phone width, and the UI passes quality through.
  await page.locator('#generatorDownloadButton').click();
  await page.locator('#generatorExportMode button[value="quality"]').click();
  assert.equal(await page.locator('#generatorExportMode').getAttribute('data-value'),'quality');
  await page.setViewportSize({width:390,height:844});
  const boxes=await page.locator('#generatorExportMode button').evaluateAll(buttons=>buttons.map(b=>({x:b.getBoundingClientRect().x,right:b.getBoundingClientRect().right,y:b.getBoundingClientRect().y})));
  assert.equal(boxes.length,3);assert.equal(boxes[1].y,boxes[2].y);assert.ok(boxes[2].x>boxes[1].x&&boxes[2].right<=390);
  await page.locator('#generatorExportClose').click();
  const cancelled=await page.evaluate(async()=>{
    const pending=GeneratorApp.exportMp4({mode:'quality',durationSeconds:15,download:false});
    await new Promise(resolve=>setTimeout(resolve,250));GeneratorApp.cancelExport();
    return (await pending)===null&&!GeneratorApp.getSummary().exporting;
  });
  assert.equal(cancelled,true);

  assert.deepEqual(errors,[]);
  console.log('Quality export regression passed: 300 layers, MP4 fidelity/seek/timing, lossless WebP, mobile choices and cancellation.');
} finally {await context.close();await browser.close();await new Promise(resolve=>server.close(resolve));}
