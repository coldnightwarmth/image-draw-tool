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
 for(const width of [1280,640]) {
  await page.setViewportSize({width,height:900});
  for(const enabled of [false,true]) {
   await page.locator('.generator-mode-checkbox[value="ellipse"]').evaluate((e,v)=>{e.checked=v;e.dispatchEvent(new Event('change',{bubbles:true}));},enabled);await settle();
   await page.locator('#generatorControlsMain').evaluate(e=>e.scrollTop=e.scrollHeight);
   const bounds=await page.locator('#generatorControlsMain').evaluate(e=>({last:e.lastElementChild.getBoundingClientRect().bottom,bottom:e.getBoundingClientRect().bottom,scrollTop:e.scrollTop}));
   assert(bounds.bottom-bounds.last<30,'No blank region below final control');assert(bounds.scrollTop>0);
   assert.equal(await page.locator('#controls').evaluate(e=>getComputedStyle(e).backdropFilter),'none');
  }
 }
 await page.screenshot({path:'/tmp/generator-sidebar.png'});
 assert.equal(errors.length,0,errors.join('\n'));console.log('PASS sidebar scrolling and bottom bounds with ellipse on/off at desktop and mobile widths');
} finally {await browser.close();await new Promise(r=>server.close(r));}
