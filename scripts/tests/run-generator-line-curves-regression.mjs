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
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {buildLinePoints, createRandom, randomizeGenerationControls, buildSequenceAssignments, readSettings, state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};
try {
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 const result=await page.evaluate(()=>{
  const settings={...testGenerator.readSettings(),width:2000,height:2000,spacing:10,lineLength:500,lineAngle:0,
   lineCurveAmount:4,lineCurveStrength:25,randomize:{}};
  const make=(amount,strength,seed=42)=>testGenerator.buildLinePoints(250,{...settings,lineCurveAmount:amount,lineCurveStrength:strength},testGenerator.createRandom(seed),{x:1000,y:1000},0);
  return {curved:make(4,25),repeat:make(4,25),other:make(4,25,43),straight:make(0,25),zero:make(4,0),weak:make(4,5)};
 });
 assert.deepEqual(result.curved,result.repeat);assert.notDeepEqual(result.curved,result.other);
 assert(result.straight.every(p=>p.y===1000));assert(result.zero.every(p=>p.y===1000));
 for(const points of Object.values(result)){assert.equal(points.length,250);assert.equal(points[0].x,750);assert.equal(points.at(-1).x,1250);assert.equal(points[0].y,1000);assert.equal(points.at(-1).y,1000);assert(points.every(p=>p.x>=0&&p.x<=2000&&p.y>=0&&p.y<=2000));}
 const signs=result.curved.map(p=>Math.sign(p.y-1000)).filter(Boolean).filter((s,i,a)=>!i||s!==a[i-1]);assert.equal(signs.length,4);
 assert(Math.max(...result.curved.map(p=>Math.abs(p.y-1000)))>Math.max(...result.weak.map(p=>Math.abs(p.y-1000))));
 const record=await page.evaluate(()=>({controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()}));
 assert('generatorLineCurveAmountSlider' in record.controls.ranges);
 await page.evaluate(record=>testGenerator.restoreCompositionRecord(record),record);
 assert.equal(errors.length,0,errors.join('\n'));console.log('PASS curve count, strength, straight lines, deterministic variation, endpoints and persistence');
} finally {await browser.close();await new Promise(r=>server.close(r));}
