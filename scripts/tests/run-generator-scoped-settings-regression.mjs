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
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {randomizeGenerationControls, buildSequenceAssignments, readSettings, state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};
try {
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 await page.evaluate(()=>window.originalNodes=Array.from(document.querySelectorAll('img.generator-stamp')));
 const before=await page.evaluate(()=>({seed:testGenerator.state.currentSeed,specs:testGenerator.captureCurrentComposition().specs}));
 const edit=async(id,value)=>{await page.locator('#'+id).evaluate((e,v)=>{e.value=v;e.dispatchEvent(new Event('input',{bubbles:true}));},String(value));await settle();};
 await edit('generatorTintAmountRandomMinSlider',80);await edit('generatorTintAmountRandomMaxSlider',95);
 const after=await page.evaluate(()=>({seed:testGenerator.state.currentSeed,specs:testGenerator.captureCurrentComposition().specs,sameNodes:originalNodes.every((n,i)=>n===document.querySelectorAll('img.generator-stamp')[i])}));
 assert.equal(after.seed,before.seed);assert(after.sameNodes);
 const omitTint=spec=>{const copy=structuredClone(spec);delete copy.tintAmount;delete copy.filter;for(const sequence of [copy.sequence,copy.suspendedSequence])if(sequence){delete sequence.filterRest;delete sequence.filterActive;}return copy;};
 assert.deepEqual(after.specs.map(omitTint),before.specs.map(omitTint));
 assert(after.specs.some((s,i)=>s.tintAmount!==before.specs[i].tintAmount));
 await edit('generatorOpacityRandomMinSlider',10);await edit('generatorOpacityRandomMaxSlider',20);
 const opacity=await page.evaluate(()=>testGenerator.captureCurrentComposition().specs);
 assert.deepEqual(opacity.map(({opacity,...rest})=>rest),after.specs.map(({opacity,...rest})=>rest));
 await edit('generatorLineCurveAmountSlider',3);await edit('generatorLineCurveStrengthSlider',30);
 const curved=await page.evaluate(()=>testGenerator.captureCurrentComposition().specs);
 for(let i=0;i<curved.length;i++){
  assert.equal(curved[i].brushSource,opacity[i].brushSource);
  assert.deepEqual(curved[i].sequence,opacity[i].sequence);
  if(curved[i].mode!=='line')assert.deepEqual(curved[i],opacity[i]);
 }
 await edit('generatorMarginSlider',25);
 const margin=await page.evaluate(()=>({seed:testGenerator.state.currentSeed,specs:testGenerator.captureCurrentComposition().specs}));
 assert.equal(margin.seed,before.seed);
 const byIndex=new Map(curved.map(s=>[s.index,s]));
 for(const spec of margin.specs){const old=byIndex.get(spec.index);assert.equal(spec.opacity,old.opacity);assert.equal(spec.tintAmount,old.tintAmount);assert.equal(spec.tintHue,old.tintHue);assert.equal(spec.rotation,old.rotation);}
 const record=await page.evaluate(()=>({controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()}));
 await page.evaluate(record=>testGenerator.restoreCompositionRecord(record),record);
 assert.deepEqual(await page.evaluate(()=>testGenerator.captureCurrentComposition().specs),record.composition.specs);
 assert.equal(errors.length,0,errors.join('\n'));console.log('PASS isolated tint, opacity, line geometry, stable seed, DOM identity, sequence assignments, and save/load');
} finally {await browser.close();await new Promise(r=>server.close(r));}
