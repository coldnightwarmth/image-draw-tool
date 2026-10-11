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
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {buildEllipsePoints, buildCompositionPoints, createRandom, randomizeGenerationControls, buildSequenceAssignments, readSettings, state, captureControlState, captureCurrentComposition, restoreCompositionRecord, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};
try {
 const app=await readFile(resolve(root,'app.js'),'utf8');
 const {runInNewContext}=await import('node:vm');
 const helpers=app.slice(app.indexOf('function getRectBoundsFromPoints('),app.indexOf('function getGridAxisPositions('));
 const geometry=runInNewContext(helpers+';({getCircleBoundsFromPoints,updateConstrainedShapePoint})', {getBaseDrawMode:mode=>mode.replace('-outline','')});
 assert.equal(geometry.getCircleBoundsFromPoints(10,20,210,80).bottom,80);
 for(const mode of ['box','circle','box-outline','circle-outline']) {
  for(const point of [{x:210,y:80},{x:-190,y:-40}]) {
   const draft={mode,anchorX:10,anchorY:20};
   geometry.updateConstrainedShapePoint(draft,point,true);
   assert.equal(Math.abs(draft.currentX-10),Math.abs(draft.currentY-20));
   geometry.updateConstrainedShapePoint(draft,point,false);
   assert.equal(draft.currentX,point.x);assert.equal(draft.currentY,point.y);
  }
 }
 const placementCode=app.slice(app.indexOf('async function placeCircleBrushes('),app.indexOf('function setShapePreviewBox('));
 const gridCode=app.slice(app.indexOf('function getGridAxisPositions('),app.indexOf('async function placeRectBrushes('));
 const placed=[];
 const placement=runInNewContext(helpers+gridCode+placementCode+';({placeCircleBrushes,placeCircleOutlineBrushes})',{
  getSpacingValue:()=>10,MAX_VISIBLE_STAMPS:10000,getVisibleStampCount:()=>0,notifyStampLimitReached:()=>{},
  throwIfTaskCancelled:()=>{},maybeYieldForPlacement:async()=>{},placeBrush:(x,y,stroke)=>{placed.push({x,y});stroke.elements.push({x,y});return true;}
 });
 for(const name of ['placeCircleBrushes','placeCircleOutlineBrushes']) {
  placed.length=0;await placement[name]({elements:[]},0,0,200,60);
  assert(placed.length>0);assert(placed.every(p=>((p.x-100)/100)**2+((p.y-30)/30)**2<=1.000001));
  assert(Math.max(...placed.map(p=>p.x))-Math.min(...placed.map(p=>p.x))>150);
 }
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=12345678`);
 await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 assert.equal(await page.locator('.generator-mode-choice').count(),5);
 assert.equal(await page.locator('.generator-mode-card .draw-mode-icon').count(),5);
 const result=await page.evaluate(()=>{
  const settings={...testGenerator.readSettings(),width:600,height:400,boxWidth:400,boxHeight:100,randomize:{boxWidth:false,boxHeight:false,boxStyle:false}};
  return ['outline','filled'].map(style=>{
   settings.boxStyle=style;
   const points=testGenerator.buildEllipsePoints(200,settings,testGenerator.createRandom(42),{x:300,y:200},0);
   return {style,count:points.length,distances:points.map(p=>((p.x-300)/200)**2+((p.y-200)/50)**2),mode:points.every(p=>p.mode==='ellipse')};
  });
 });
 for(const row of result){assert.equal(row.count,200);assert(row.mode);assert(row.distances.every(d=>d<=1.000001));if(row.style==='outline')assert(row.distances.every(d=>Math.abs(d-1)<.000001));}
 assert.equal(errors.length,0,errors.join('\n'));console.log('PASS ellipse geometry, Shift constraints in both drag directions, and five generator icons');
} finally {await browser.close();await new Promise(r=>server.close(r));}
