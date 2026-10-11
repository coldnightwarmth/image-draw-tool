import assert from 'node:assert/strict';
import {chromium} from 'playwright';
import {createServer} from 'node:http';
import {readFile,writeFile,mkdtemp,mkdir,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {resolve,extname} from 'node:path';
import {fileURLToPath} from 'node:url';
const fixtureDirectory=await mkdtemp(resolve(tmpdir(),'generator-uploads-'));
const root=fileURLToPath(new URL('../../',import.meta.url));
const server=createServer(async(req,res)=>{try{let path=decodeURIComponent(new URL(req.url,'http://localhost').pathname);if(path.endsWith('/'))path+='index.html';path=resolve(root,'.'+path);if(!path.startsWith(root))throw Error();const data=await readFile(path);res.writeHead(200,{'Content-Type':({'.js':'text/javascript','.mjs':'text/javascript','.html':'text/html','.css':'text/css','.gif':'image/gif','.wasm':'application/wasm'})[extname(path)]||'application/octet-stream'});res.end(data);}catch{res.writeHead(404);res.end();}});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const browser=await chromium.launch({headless:true,...(process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH?{executablePath:process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH}:{})});
const page=await browser.newPage();const errors=[];page.on('pageerror',e=>errors.push(e.message));
await page.route('**/generator.js?*',async route=>{const response=await route.fetch();await route.fulfill({response,body:(await response.text()).replace('  window.GeneratorApp = {','  window.testGenerator = {hslToHex, state, captureControlState, captureCurrentComposition, restoreCompositionRecord, createBookmarkBackupBlob, normalizeBookmarkBackupRecord, bookmarkCurrentComposition, applyPendingDynamicUpdate};\n  window.GeneratorApp = {')});});
const settle=async()=>{await page.waitForTimeout(200);await page.evaluate(()=>testGenerator.applyPendingDynamicUpdate());await page.waitForFunction(()=>!testGenerator.state.generating&&!testGenerator.state.dynamicUpdateBase);};
try{
 await page.goto(`http://127.0.0.1:${server.address().port}/generator/?seed=1234abcd`);await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);
 assert(await page.locator('#generatorTintColorRandomToggle').isChecked());
 // Dragging inside a selected range translates both ends; handles remain independent.
 const opacityRange=page.locator('[data-random-range="opacity"]');
 await opacityRange.scrollIntoViewIfNeeded();
 const rangeValues=()=>opacityRange.locator('input').evaluateAll(es=>es.map(e=>Number(e.value)));
 const savedOpacityRange=await rangeValues();
 await opacityRange.locator('input').evaluateAll(es=>{es[0].value='20';es[1].value='60';es[0].dispatchEvent(new Event('input',{bubbles:true}));});
 const rangeRect=await opacityRange.boundingBox(), dragX=rangeRect.x+rangeRect.width*39/99, dragY=rangeRect.y+11;
 await page.mouse.move(dragX,dragY);await page.mouse.down();
 await page.mouse.move(dragX+rangeRect.width*20/99,dragY);assert.deepEqual(await rangeValues(),[40,80]);
 await page.mouse.move(dragX+rangeRect.width*2,dragY);assert.deepEqual(await rangeValues(),[60,100]);
 await page.mouse.move(dragX-rangeRect.width*2,dragY);assert.deepEqual(await rangeValues(),[1,41]);await page.mouse.up();
 assert.equal(await opacityRange.evaluate(e=>e.classList.contains('is-dragging-range')),false);
 await page.mouse.move(rangeRect.x+rangeRect.width*40/99,dragY);await page.mouse.down();
 await page.mouse.move(rangeRect.x+rangeRect.width*70/99,dragY);await page.mouse.up();assert.deepEqual(await rangeValues(),[1,71]);
 await opacityRange.locator('input').evaluateAll((es,values)=>{es.forEach((e,i)=>e.value=values[i]);es[0].dispatchEvent(new Event('input',{bubbles:true}));},savedOpacityRange);await settle();

 assert.equal(await page.locator('#generatorBackgroundColorInput').inputValue(),await page.evaluate(()=>testGenerator.state.currentBackground));
 // A future-randomization switch can be changed while a live slider edit is queued.
 await page.evaluate(()=>{
   const slider=document.querySelector('#generatorTintAmountRandomMaxSlider');
   slider.dispatchEvent(new Event('input',{bubbles:true}));
   if (!testGenerator.state.dynamicUpdateBase) throw Error('Expected pending live update');
   const toggle=document.querySelector('#generatorCountRandomToggle');
   toggle.dispatchEvent(new Event('change',{bubbles:true}));
 });await settle();

 const specsBefore=await page.evaluate(()=>JSON.stringify(testGenerator.captureCurrentComposition().specs));
 await page.locator('#generatorBackgroundColorInput').evaluate(e=>{e.value='#123456';e.dispatchEvent(new Event('input',{bubbles:true}));});await page.waitForTimeout(150);
 assert(await page.locator('#generatorBackgroundRandomToggle').isChecked());assert.equal(await page.evaluate(()=>testGenerator.state.currentBackground),'#123456');
 assert.equal(await page.evaluate(()=>JSON.stringify(testGenerator.captureCurrentComposition().specs)),specsBefore);
 await page.evaluate(()=>GeneratorApp.randomizeBackground());assert.equal(await page.locator('#generatorBackgroundColorInput').inputValue(),await page.evaluate(()=>testGenerator.state.currentBackground));
 const original=await page.evaluate(()=>{window.originalNodes=Array.from(document.querySelectorAll('.generator-stamp'));return testGenerator.captureCurrentComposition().specs;});
 const effect=original.find(s=>s.sequence)?.sequence.effect;assert(effect);
 await page.locator(`.generator-sequence-effect-checkbox[value="${effect}"]`).uncheck({force:true});await settle();
 const off=await page.evaluate(()=>testGenerator.captureCurrentComposition().specs);
 for(let i=0;i<original.length;i++){if(original[i].sequence?.effect===effect){assert.equal(off[i].sequence,null);assert.deepEqual(off[i].suspendedSequence,original[i].sequence);}else assert.deepEqual(off[i].sequence,original[i].sequence);}
 await page.locator(`.generator-sequence-effect-checkbox[value="${effect}"]`).check({force:true});await settle();
 assert.deepEqual((await page.evaluate(()=>testGenerator.captureCurrentComposition().specs)).map(s=>s.sequence),original.map(s=>s.sequence));
 assert(await page.evaluate(()=>originalNodes.every((n,i)=>n===document.querySelectorAll('.generator-stamp')[i])));
 // Disabled assignments survive other sequence edits, saves, and master toggles.
 await page.locator(`.generator-sequence-effect-checkbox[value="${effect}"]`).uncheck({force:true});await settle();
 await page.locator('#generatorSequenceSpeedSlider').evaluate(e=>{e.value='85';e.dispatchEvent(new Event('input',{bubbles:true}));});await settle();
 const suspendedRecord=await page.evaluate(()=>({controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()}));
 assert.deepEqual(suspendedRecord.composition.specs.filter(s=>s.suspendedSequence).map(s=>s.suspendedSequence),original.filter(s=>s.sequence?.effect===effect).map(s=>s.sequence));
 await page.evaluate(record=>testGenerator.restoreCompositionRecord(record),suspendedRecord);
 await page.locator(`.generator-sequence-effect-checkbox[value="${effect}"]`).check({force:true});await settle();
 const beforeMaster=await page.evaluate(()=>testGenerator.captureCurrentComposition().specs.map(s=>s.sequence));
 await page.locator('#generatorSequenceEnabledToggle').uncheck({force:true});await settle();
 assert(await page.evaluate(()=>testGenerator.state.currentSpecs.every(s=>!s.sequence)));
 await page.locator('#generatorSequenceEnabledToggle').check({force:true});await settle();
 assert.deepEqual(await page.evaluate(()=>testGenerator.captureCurrentComposition().specs.map(s=>s.sequence)),beforeMaster);
 // Saved legacy specs are rendered verbatim; absent new controls inherit old tint behavior.
 const legacy=await page.evaluate(()=>({controls:testGenerator.captureControlState(),composition:testGenerator.captureCurrentComposition()}));delete legacy.controls.randomize.tintColor;legacy.controls.randomize.tint=false;
 await page.evaluate(record=>testGenerator.restoreCompositionRecord(record),legacy);assert(!(await page.locator('#generatorTintColorRandomToggle').isChecked()));
 assert.deepEqual((await page.evaluate(()=>testGenerator.captureCurrentComposition().specs)).map(s=>s.sequence),legacy.composition.specs.map(s=>s.sequence));
 await page.locator('#generatorUploadTab').click();
 const png=await page.evaluate(()=>{const c=document.createElement('canvas');c.width=40;c.height=20;const ctx=c.getContext('2d');ctx.fillStyle='#ff4422';ctx.fillRect(0,0,40,20);return c.toDataURL().split(',')[1];});
 const gif=Buffer.from('R0lGODlhGAAYAIEAAOYeKAAAAAAAAAAAACH/C05FVFNDQVBFMi4wAwEAAAAh+QQACgAAACwAAAAAGAAYAAAIKQABCBxIsKDBgwgTKlzIsKHDhxAjSpxIsaLFixgzatzIsaPHjyBDPgwIACH5BAEUAAEALAAAAAAYABgAgR4e5gAAAAAAAAAAAAgpAAEIHEiwoMGDCBMqXMiwocOHECNKnEixosWLGDNq3Mixo8ePIEM+DAgAOw==','base64');
 await page.locator('#generatorUploadImagesInput').setInputFiles([{name:'wide.png',mimeType:'image/png',buffer:Buffer.from(png,'base64')},{name:'animated.gif',mimeType:'image/gif',buffer:gif},{name:'broken.png',mimeType:'image/png',buffer:Buffer.from('broken')}]);
 await page.waitForFunction(()=>testGenerator.state.uploadedSources.length===2);await settle();
 assert.match(await page.locator('#generatorUploadStatus').textContent(),/1 unreadable/);
 assert(await page.evaluate(()=>testGenerator.state.currentSpecs.every(s=>s.brush.source.startsWith('upload:'))));
 // Drop real files, then simulate the browser's batched, nested directory entries.
 await page.evaluate(({png,gif})=>{
   const file=(name,data,type)=>new File([Uint8Array.from(atob(data),c=>c.charCodeAt(0))],name,{type});
   const transfer=new DataTransfer();
   transfer.items.add(file('dropped.png',png,'image/png'));
   transfer.items.add(file('dropped.gif',gif,'image/gif'));
   document.querySelector('#generatorUploadDropZone').dispatchEvent(new DragEvent('drop',{bubbles:true,cancelable:true,dataTransfer:transfer}));
 },{png,gif:gif.toString('base64')});
 await page.waitForFunction(()=>!testGenerator.state.uploadingSources);await settle();
 assert.equal(await page.locator('#generatorUploadStatus').textContent(),'2 images ready');
 await page.evaluate(({png,gif})=>{
   const fileEntry=(name,data,type)=>({isFile:true,file:resolve=>resolve(new File([Uint8Array.from(atob(data),c=>c.charCodeAt(0))],name,{type}))});
   const directory=batches=>({isDirectory:true,createReader:()=>{let index=0;return {readEntries:resolve=>resolve(batches[index++]||[])};}});
   const root=directory([[fileEntry('nested.png',png,'image/png')],[directory([[fileEntry('nested.gif',gif,'image/gif')]])]]);
   const event=new Event('drop',{bubbles:true,cancelable:true});
   Object.defineProperty(event,'dataTransfer',{value:{items:[{kind:'file',webkitGetAsEntry:()=>root,getAsFile:()=>null}],files:[]}});
   document.querySelector('#generatorUploadDropZone').dispatchEvent(event);
 },{png,gif:gif.toString('base64')});
 await page.waitForFunction(()=>!testGenerator.state.uploadingSources);await settle();
 assert.equal(await page.locator('#generatorUploadStatus').textContent(),'2 images ready');
 assert.equal(await page.evaluate(()=>testGenerator.state.uploadedSources.length),2);
 await mkdir(resolve(fixtureDirectory,'nested'));
 await writeFile(resolve(fixtureDirectory,'wide.png'),Buffer.from(png,'base64'));
 await writeFile(resolve(fixtureDirectory,'nested/animated.gif'),gif);
 await page.locator('#generatorUploadFolderInput').setInputFiles(fixtureDirectory);
 await page.waitForFunction(()=>document.querySelector('#generatorUploadStatus').textContent==='2 images ready');await settle();
 await page.screenshot({path:'/tmp/generator-upload-desktop.png',fullPage:true});
 await page.setViewportSize({width:390,height:844});
 await page.locator('#generatorUploadTab').scrollIntoViewIfNeeded();
 assert(await page.locator('#generatorUploadImages').isVisible());
 assert(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth));
 await page.screenshot({path:'/tmp/generator-upload-mobile.png'});
 await page.setViewportSize({width:1280,height:900});
 await page.locator('#generatorCountSlider').evaluate(e=>{e.value='5';e.dispatchEvent(new Event('input',{bubbles:true}));});
 await page.locator('#generatorTintRandomToggle').uncheck({force:true});await page.locator('#generatorTintColorRandomToggle').check({force:true});await settle();
 await page.evaluate(()=>GeneratorApp.generate(42));const hues=await page.evaluate(()=>testGenerator.state.currentSpecs.map(s=>s.tintHue));
 const randomPicker=await page.locator('#generatorTintColorInput').inputValue();
 assert.equal(randomPicker,await page.evaluate(()=>{const sample=testGenerator.state.currentSpecs.reduce((a,b)=>a.index<b.index?a:b);return testGenerator.hslToHex(sample.tintHue,84,54);}));
 await page.evaluate(()=>GeneratorApp.generate(43));assert.notEqual(await page.locator('#generatorTintColorInput').inputValue(),randomPicker);

 await page.evaluate(()=>GeneratorApp.generate(42));assert.deepEqual(await page.evaluate(()=>testGenerator.state.currentSpecs.map(s=>s.tintHue)),hues);assert(new Set(hues).size>1, JSON.stringify({hues,summary:await page.evaluate(()=>GeneratorApp.getSummary())}));
 await page.locator('#generatorTintColorRandomToggle').uncheck({force:true});await settle();assert.equal((new Set(await page.evaluate(()=>testGenerator.state.currentSpecs.map(s=>s.tintHue)))).size,1);
 await page.evaluate(()=>testGenerator.bookmarkCurrentComposition());
 const backup=await page.evaluate(async()=>JSON.parse(await (await testGenerator.createBookmarkBackupBlob()).text()));assert(backup.bookmarks.some(b=>b.composition.uploadedAssets?.length===2));
 const uploadRecord=backup.bookmarks.find(b=>b.composition.uploadedAssets?.length===2);
 await page.reload();await page.waitForFunction(()=>window.testGenerator?.state.currentSpecs.length>0&&!testGenerator.state.generating);assert.equal(await page.evaluate(()=>testGenerator.state.sourceMode),'upload');
 assert(await page.evaluate(()=>testGenerator.state.currentSpecs.every(s=>s.brush.dataUrl)));
 await page.evaluate(async record=>{for(const a of record.composition.uploadedAssets)testGenerator.state.catalogBySource.delete(a.source);const restored=await testGenerator.normalizeBookmarkBackupRecord(record);await testGenerator.restoreCompositionRecord(restored);},uploadRecord);
 const out=await page.evaluate(async()=>{const r=await GeneratorApp.exportWebp({mode:'quality',durationSeconds:1,download:false,returnBlob:true});if(!r)throw Error(document.querySelector('#generatorExportStatus').textContent);return {bytes:r.blob.size,frames:r.frameCount};});assert(out.bytes>100);assert.equal(out.frames,50);
 assert.deepEqual(errors,[]);console.log('Generator upload/control regression passed',out);
}finally{await browser.close();server.close();await rm(fixtureDirectory,{recursive:true,force:true});}
