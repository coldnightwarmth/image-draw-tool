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
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};try {
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 const current=()=>page.evaluate(()=>testGenerator.captureCurrentComposition());
 const initial=await current();
 await page.evaluate(()=>GeneratorApp.randomizeBackground('#123456'));const first=await current();
 await page.evaluate(()=>GeneratorApp.randomizeBackground('#abcdef'));const second=await current();
 assert(await page.evaluate(()=>GeneratorApp.undo()));assert.deepEqual(await current(),first);
 assert(await page.evaluate(()=>GeneratorApp.undo()));assert.deepEqual(await current(),initial);
 assert.equal(await page.evaluate(()=>GeneratorApp.getSummary().historyDepth),0);
 assert(await page.locator('#generatorUndoButton').isVisible());
 await page.locator('#generatorUndoButton').click();assert.deepEqual(await current(),initial);
 await page.locator('#generatorUndoButton').click({button:'right'});
 await page.waitForFunction(()=>!testGenerator.state.applyingHistory);assert.deepEqual(await current(),first);
 await page.locator('#generatorUndoButton').click({modifiers:['Control']});
 await page.waitForFunction(()=>!testGenerator.state.applyingHistory);assert.deepEqual(await current(),second);
 await page.locator('#generatorUndoButton').click();
 await page.waitForFunction(()=>!testGenerator.state.applyingHistory);assert.deepEqual(await current(),first);
 await page.reload();await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.restoringActiveSession);
 assert.equal(await page.evaluate(()=>GeneratorApp.getSummary().redoDepth),1);
 assert(await page.evaluate(()=>GeneratorApp.redo()));assert.deepEqual(await current(),second);
 assert(await page.evaluate(()=>GeneratorApp.undo()));
 await page.evaluate(()=>GeneratorApp.randomizeBackground('#654321'));const branched=await current();
 assert.equal(await page.evaluate(()=>GeneratorApp.redo()),false);assert.deepEqual(await current(),branched);
 // Undo a queued edit; redo must recover the edited rendering, not just its inputs.
 const beforeQueued=await current();
 await page.evaluate(async()=>{
   const slider=document.querySelector('#generatorTintAmountRandomMaxSlider');slider.value='99';slider.dispatchEvent(new Event('input',{bubbles:true}));
   await GeneratorApp.undo();
 });assert.deepEqual(await current(),beforeQueued);
 assert(await page.evaluate(()=>GeneratorApp.redo()));
 assert.equal(await page.locator('#generatorTintAmountRandomMaxSlider').inputValue(),'99');
 assert.notDeepEqual((await current()).specs,beforeQueued.specs);
 assert.deepEqual(errors,[]);
 console.log('Redo regression passed: normal undo, right-click/Control-click redo, empty undo stack, reload, branching, queued edits');
} finally {await browser.close();server.close();}
