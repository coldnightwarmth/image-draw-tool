#!/usr/bin/env node
import assert from 'node:assert/strict';
import { fitCollage, normalizeSettings, describePixels, PRESETS } from '../../photo/matcher.mjs';
const width = 72, height = 60;
const pixels = new Uint8ClampedArray(width * height * 4);
for(let y = 0; y < height; y++) for(let x = 0; x < width; x++) pixels.set([x < 36 ? 220 : 20, y < 30 ? 20 : 220, 40, 255], (y * width + x) * 4);
const assets = [[220,20,40], [20,20,40], [220,220,40], [20,220,40]].map((color, index) => {
  const rgba = new Uint8ClampedArray(32 * 32 * 4);
  for(let y=0;y<32;y++) for(let x=0;x<32;x++) rgba.set([...color, index===3 && (x<4||y<4)?0:255],(y*32+x)*4);
  return {id:String(index),tileSize:32,pixels:rgba,...describePixels(rgba)};
});
const settings = {...PRESETS.detailed,count:300,size:12,resemblance:100};
const input = {width,height,pixels,assets,settings,seed:123};
const a = await fitCollage(input), b = await fitCollage(input);
assert.deepEqual(a.entries,b.entries,'a seed reproduces the exact composition');
assert.deepEqual(a.pixels,b.pixels);
assert(a.error < a.baseError * .2, `matching reduces reconstruction error: ${a.error}/${a.baseError}`);
const refined = await fitCollage({...input,initial:a.entries,background:a.background,settings:{...settings,count:a.entries.length+100}});
assert(refined.error <= a.error,'refinement cannot increase the objective error');
assert.deepEqual(refined.entries.slice(0,a.entries.length), a.entries,'refinement preserves earlier placements');
const grid = await fitCollage({...input,settings:{...settings,count:25,grid:true}});
const columns=Math.round(Math.sqrt(25*width/height)), rows=Math.floor(25/columns);
assert.equal(grid.entries.length,columns*rows);
for(const e of grid.entries) {
 assert.equal(e.rotation,0);
 assert(Math.abs(e.x*columns-.5-Math.round(e.x*columns-.5))<1e-8);
 assert(Math.abs(e.y*rows-.5-Math.round(e.y*rows-.5))<1e-8);
 assert.equal(e.size, Math.min(width/columns,height/rows)/Math.min(width,height));
}
await assert.rejects(()=>fitCollage({...input,assets:[]}),/Choose at least one/);
await assert.rejects(()=>fitCollage(input,{cancelled:()=>true}),{name:'AbortError'});
assert.equal(normalizeSettings({count:Infinity,size:0,rotation:800}).size,1);
assert.equal(normalizeSettings({rotation:800}).rotation,180);
assert.equal(normalizeSettings({count:-1}).count,25);
const skinny = await fitCollage({...input, width:300, height:2, pixels:new Uint8ClampedArray(300*2*4).fill(255),settings:{...settings,grid:true,count:25}});
assert(skinny.entries.length<=25,'extreme aspect ratios still respect the grid budget');
console.log(JSON.stringify({passed:true,placements:a.entries.length,errorReduction:1-a.error/a.baseError,refinedError:refined.error,grid: grid.entries.length}));
