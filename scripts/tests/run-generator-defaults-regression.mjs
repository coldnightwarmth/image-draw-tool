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
 const checkDefaults=async()=>{
  for(const key of ['Rotation','Pitch','Yaw','HorizontalStretch','VerticalStretch']) assert.equal(await page.locator(`#generator${key}RandomToggle`).isChecked(),false,key);
  for(const key of ['Count','MarkCount','GifsPerMark','Margin','MarginMode','Gif']) assert(await page.locator(`#generator${key}RandomToggle`).isChecked(),key);
  for(const key of ['SequenceEffects','SequenceNoneFrequency']) assert(await page.locator(`#generator${key}RandomToggle`).isChecked(),key);
  assert(await page.evaluate(()=>Array.from(document.querySelectorAll('.generator-range-random-checkbox')).every(input=>{
   const propertyToggle=document.getElementById(input.id.replace('RangeRandomToggle','RandomToggle'));
   return input.checked === (propertyToggle ? propertyToggle.defaultChecked : true);
  })));
  assert.equal(await page.locator('#generatorMarginSlider').inputValue(),'0');
  assert(await page.locator('input[name="generatorMarginMode"][value="placement"]').isChecked());
 };
 await checkDefaults();
 assert(await page.evaluate(()=>document.querySelector('#generatorSampleDetails .generator-sidebar-details-body').firstElementChild.classList.contains('generator-different-gif-group')));
 assert(await page.evaluate(()=>document.querySelector('#generatorControlsMain').lastElementChild.contains(document.querySelector('#generatorSmoothPreviewToggle'))));
 await page.locator('label.ios-switch[for="generatorGifRandomToggle"]').click();await settle();
 assert(await page.locator('.generator-count-group').isHidden());
 assert(await page.locator('.generator-gifs-per-mark-group').isHidden());
 await page.locator('[data-randomization-preset="on"]').click();await settle();
 await page.locator('input[name="generatorMarginMode"][value="crop"]').evaluate(e=>{e.checked=true;e.dispatchEvent(new Event('change',{bubbles:true}));});
 await page.locator('#generatorMarginSlider').evaluate(e=>{e.value='25';e.dispatchEvent(new Event('input',{bubbles:true}));});await settle();
 await page.locator('[data-randomization-preset="default"]').click();await settle();
 await checkDefaults();
 assert(await page.locator('.generator-count-group').isVisible());
 const frequencies=await page.evaluate(()=>{
  const slider=document.getElementById('generatorSequenceNoneFrequencySlider');
  const toggle=document.getElementById('generatorSequenceNoneFrequencyRandomToggle');
  const values=[];for(let seed=1;seed<=10;seed++){testGenerator.randomizeGenerationControls(seed);values.push(Number(slider.value));}
  testGenerator.randomizeGenerationControls(1);const repeated=Number(slider.value);
  toggle.checked=false;slider.value='37';testGenerator.randomizeGenerationControls(999);
  return {values,repeated,manual:Number(slider.value),saved:testGenerator.captureControlState().generationRandomize.noneFrequency};
 });
 assert(frequencies.values.every(v=>v>=0&&v<=99));assert(new Set(frequencies.values).size>1);
 assert.equal(frequencies.repeated,frequencies.values[0]);assert.equal(frequencies.manual,37);assert.equal(frequencies.saved,false);
 assert.equal(errors.length,0,errors.join('\n'));
 console.log('PASS generator defaults, control placement, and sample-count visibility');
} finally {await browser.close();await new Promise(r=>server.close(r));}
