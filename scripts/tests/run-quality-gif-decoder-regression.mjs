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
  await page.goto(url,{waitUntil:'load'});
  const result=await page.evaluate(async()=>{
    const {QualityGifDecoder}=await import('/generator/quality-gif-decoder.mjs');
    // Small delta-frame GIF exercises both background and restore-previous disposal.
    const bytes=[...new TextEncoder().encode('GIF89a'),3,0,2,0,0x81,0,0, 0,0,0, 255,0,0, 0,0,255, 0,255,0];
    const delays=[20,30,50,70,30,40];
    const add=(left,top,width,height,pixels,disposal,index)=>{
      bytes.push(0x21,0xf9,4,(disposal<<2)|1,delays[index]/10,0,0,0,0x2c,left,0,top,0,width,0,height,0,0,2);
      const codes=pixels.flatMap(pixel=>[4,pixel]);codes.push(5);
      const packed=[];let value=0,bits=0;
      for(const code of codes){value|=code<<bits;bits+=3;while(bits>=8){packed.push(value&255);value>>>=8;bits-=8;}}
      if(bits)packed.push(value);bytes.push(packed.length,...packed,0);
    };
    add(0,0,3,2,[1,1,1,1,1,1],1,0);
    add(0,0,1,1,[2],3,1);
    add(1,0,1,1,[3],2,2);
    add(2,0,1,1,[2],1,3);
    add(0,0,1,1,[0],1,4);
    add(0,0,3,2,[3,1,2,1,2,3],1,5);bytes.push(0x3b);
    const buffer=new Uint8Array(bytes).buffer;
    const native=new ImageDecoder({data:buffer,type:'image/gif'});
    const expected=[];
    const canvas=new OffscreenCanvas(3,2),ctx=canvas.getContext('2d',{willReadFrequently:true});
    try {for(let frameIndex=0;frameIndex<6;frameIndex++){
      const {image}=await native.decode({frameIndex});ctx.clearRect(0,0,3,2);ctx.drawImage(image,0,0);image.close();
      expected.push(Array.from(ctx.getImageData(0,0,3,2).data));
    }} finally {native.close();}
    let allocated=0,budget=Infinity,evictions=0,cancelled=false,peak=0;
    const decoder=new QualityGifDecoder({
      reserve:bytes=>{while(allocated+bytes>budget&&decoder.evictOne())evictions++;if(allocated+bytes>budget)throw Error('Budget exceeded');allocated+=bytes;peak=Math.max(peak,allocated);},
      release:bytes=>{allocated-=bytes;},check:()=>{if(cancelled)throw new DOMException('Cancelled','AbortError');},
      yieldWork:()=>Promise.resolve(),backgroundColor:()=>'',frameDelay:frame=>Math.max(20,frame.gce.delay*10),byteLength:(w,h)=>w*h*4
    });
    const assets=Array.from({length:8},(_,id)=>decoder.prepare(buffer,String(id)));
    const compressedBytes=allocated;
    budget=allocated+assets[0].workingBytes*2;peak=allocated;
    let comparisons=0;
    for(const time of [0,20,50,100,170,200,20,0,-20,260]) {
      for(const asset of assets) {
        const source=await decoder.resolve(asset,time);
        ctx.clearRect(0,0,3,2);ctx.drawImage(source,0,0);decoder.pinned=null;
        let remaining=(time%240+240)%240,index=0;
        while(index<5&&remaining>=delays[index])remaining-=delays[index++];
        if(JSON.stringify(Array.from(ctx.getImageData(0,0,3,2).data))!==JSON.stringify(expected[index]))throw Error('GIF disposal/cache pixel mismatch at '+time);
        comparisons++;
      }
    }
    if(!evictions||peak>budget)throw Error('Cache did not stay bounded');
    cancelled=true;
    let aborted=false;try{await decoder.resolve(assets[0],0);}catch(error){aborted=error.name==='AbortError';}
    if(!aborted)throw Error('Decode cancellation ignored');
    decoder.clear();if(allocated!==compressedBytes)throw Error('Decode cache leaked');
    return {comparisons,evictions,budget,peak};
  });
  assert.deepEqual(errors,[]);
  console.log('Quality native GIF decoder passed:',JSON.stringify(result));
} finally {await context.close();await browser.close();await new Promise(resolve=>server.close(resolve));}
