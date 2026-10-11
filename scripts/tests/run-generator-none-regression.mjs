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
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {buildSequenceAssignments, readSettings, state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};
try {
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 assert.equal(await page.locator('#generatorSequenceHint').count(),0);
 const none=page.locator('.generator-sequence-effect-checkbox[value="none"]'), slider=page.locator('#generatorSequenceNoneFrequencySlider');
 assert.equal(await slider.getAttribute('max'),'99');assert(await slider.isDisabled());
 const original=await page.evaluate(()=>testGenerator.captureCurrentComposition().specs);
 const setFrequency=async value=>{await slider.evaluate((e,v)=>{e.value=v;e.dispatchEvent(new Event('input',{bubbles:true}));},String(value));await settle();};
 await none.check();await setFrequency(50);
 const muted=await page.evaluate(()=>testGenerator.captureCurrentComposition().specs);
 assert(muted.some(s=>s.noneAssigned));assert(muted.some(s=>!s.noneAssigned));
 for(let i=0;i<muted.length;i++) {
  if(muted[i].noneAssigned){assert.equal(muted[i].sequence,null);assert.deepEqual(muted[i].suspendedSequence,original[i].sequence);}
  else assert.deepEqual(muted[i].sequence,original[i].sequence);
 }
 const record=await page.evaluate(()=>({controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()}));
 await page.evaluate(record=>testGenerator.restoreCompositionRecord(record),record);
 assert.equal(await slider.inputValue(),'50');assert(await none.isChecked());
 assert.deepEqual(await page.evaluate(()=>testGenerator.captureCurrentComposition().specs.map(s=>s.noneAssigned)),muted.map(s=>s.noneAssigned));
 await setFrequency(0);assert(await page.evaluate(()=>testGenerator.state.currentSpecs.every(s=>s.sequence&&!s.noneAssigned)));
 assert.deepEqual(await page.evaluate(()=>testGenerator.captureCurrentComposition().specs.map(s=>s.sequence)),original.map(s=>s.sequence));
 await setFrequency(99);await none.uncheck();await settle();
 assert.deepEqual(await page.evaluate(()=>testGenerator.captureCurrentComposition().specs.map(s=>s.sequence)),original.map(s=>s.sequence));
 const distribution=await page.evaluate(()=>{
  const settings=testGenerator.readSettings();settings.sequence.effects=['move','none'];settings.sequence.noneFrequency=70;
  const base=testGenerator.state.currentSpecs[0];let none=0,total=0;let deterministic=true;
  for(let seed=0;seed<100;seed++) {
   const make=()=>Array.from({length:64},(_,i)=>({...base,index:i,motifId:i,sequence:null,suspendedSequence:null}));
   const specs=make();testGenerator.buildSequenceAssignments(specs,settings,seed);
   const same=make();testGenerator.buildSequenceAssignments(same,settings,seed);
   deterministic&&=JSON.stringify(specs.map(s=>s.noneAssigned))===JSON.stringify(same.map(s=>s.noneAssigned));
   none+=specs.filter(s=>s.noneAssigned).length;total+=specs.length;
  }return {frequency:none/total,deterministic};
 });assert(distribution.frequency>.67&&distribution.frequency<.73,JSON.stringify(distribution));assert(distribution.deterministic);
 assert.deepEqual(errors,[]);console.log('None sequence regression passed',distribution);
} finally {await browser.close();server.close();}
