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
const url = `http://127.0.0.1:${server.address().port}/`;
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ viewport: { width: 1280, height: 900 }, acceptDownloads: true });
const page = await context.newPage();
page.setDefaultTimeout(30000);
const errors = [];
page.on('pageerror', error => errors.push(error.message));
try {
  await page.goto(url, {waitUntil:'load'});
  const result = await page.evaluate(async () => {
    const {parseGIF, decompressFrames} = await import('/gifuct-js.bundle.mjs');
    const delays = Array.from({length:60}, (_,i) => [20,30,70,100][i%4]);
    // Real animated source with variable frame delays, not a mocked timing map.
    const sourceEncoder = createIncrementalGifEncoder(8,8,true,null);
    for(let i=0;i<delays.length;i++) {
      const pixels=new Uint8ClampedArray(8*8*4);
      for(let p=0;p<pixels.length;p+=4) { const red=(i+Math.floor(p/128))%2; pixels[p]=red?255:0; pixels[p+2]=red?0:255; pixels[p+3]=255; }
      await sourceEncoder.addFrame(new ImageData(pixels,8,8),{delay:delays[i],last:i===delays.length-1});
    }
    const source=sourceEncoder.finish();
    const src=URL.createObjectURL(source);
    const bounds={left:0,top:0,right:1024,bottom:1024};
    const entry={sourceUrl:src,centerX:512,centerY:512,width:1024,height:1024,opacity:1,rotation:0};
    try {
      const output=await renderExportGifBlobWithRasterWorker(bounds,1024,1024,[entry],{includeBackground:true,animationAuto:true});
      const frames=decompressFrames(parseGIF(await output.arrayBuffer()),false);
      const actual=frames.map(f=>f.delay);
      if(JSON.stringify(actual)!==JSON.stringify(delays))throw Error('Variable delays changed: '+actual);
      if(frames.some((f,i)=>{const c=f.colorTable[f.pixels[0]];return i%2 ? c[0]<200||c[2]>30 : c[2]<200||c[0]>30;}))throw Error('Incorrect animated frame samples: '+JSON.stringify(frames.slice(0,4).map(f=>[f.colorTable[f.pixels[0]], f.colorTable[f.pixels[512*1024+512]]])));
      const limited=createExportFrameDelays(30000);
      if(limited.reduce((a,b)=>a+b,0)!==30000 || Math.max(...limited)>70)throw Error('Frame cap freezes final frame');
      const manual=createExportFrameDelaysForCount(1000,30);
      if(manual.reduce((a,b)=>a+b,0)!==1000 || manual.some(n=>n%10))throw Error('Centisecond rounding drift');
      // Fallback exporter has the same incremental encoder and timing behavior.
      const small={left:0,top:0,right:8,bottom:8};
      const map=new Map([[src,{frames:Array(4).fill(null),durations:[20,30,70,100],totalDuration:220}]]);
      const fallback=await renderExportGifBlob(small,8,8,[],{includeBackground:false,gifAnimationMap:map,sourceImagesLoaded:true,animationAuto:true});
      const fallbackDelays=decompressFrames(parseGIF(await fallback.arrayBuffer()),false).map(f=>f.delay);
      if(JSON.stringify(fallbackDelays)!=='[20,30,70,100]')throw Error('Fallback timing mismatch');
      const task={cancelled:false};
      const encoder=createIncrementalGifEncoder(1024,1024,true,task);
      const pending=encoder.addFrame(new ImageData(1024,1024),{delay:20,last:true});
      task.cancelled=true;encoder.abort();
      let cancelled=false;try{await pending;}catch{cancelled=true;}
      if(!cancelled||task.gif!==null)throw Error('Cancellation did not release encoder');
      return {frames:frames.length,duration:actual.reduce((a,b)=>a+b,0),size:output.size,fallbackDelays};
    } finally {URL.revokeObjectURL(src);}
  });
  assert.deepEqual(errors,[]);
  console.log('Main GIF timing regression passed:',JSON.stringify(result));
} finally {await context.close();await browser.close();await new Promise(resolve=>server.close(resolve));}
