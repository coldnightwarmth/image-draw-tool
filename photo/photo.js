import { DEFAULTS, PRESETS, normalizeSettings } from './matcher.mjs?v=20261009-photo-v1';
import { RasterSession, createScene } from './raster-client.mjs?v=20261009-photo-memory-v2';
import { renderExport } from './export.mjs?v=20261009-photo-memory-v2';

const $ = id => document.getElementById(id);
const state = {
  settings: { ...DEFAULTS }, seed: 0x1a2b3c4d, sourceMode: 'stock', categories: new Set(),
  catalog: new Map(), stock: [], local: [], reference: null, composition: null,
  fitting: false, importing: false, exporting: false, paused: false, timeMs: 0, displayedTimeMs: 0,
  fitId: 0, importId: 0, referenceId: 0, previewId: 0, ready: false, format: 'mp4', suspended: false
};
let worker, preview, previewTimer, fitTimer, exportAbort, folderHandle, referenceURL, pendingLocal = [];
let previousProgress = null, previewReady = false;
const context = $('photoCanvas').getContext('2d', { alpha: false });
const status = (text, error = false) => { $('photoStatus').textContent = text; $('photoStatus').classList.toggle('is-error', error); };
const exportStatus = (text, error = false) => { $('exportStatus').textContent = text; $('exportStatus').classList.toggle('is-error', error); };
const pressed = (id, value) => { for (const button of $(id).querySelectorAll('button')) button.setAttribute('aria-pressed', String(button.value === value)); };
const sourceURL = source => new URL('../' + source.split('/').map(encodeURIComponent).join('/'), location.href).href;
const selectedAssets = () => [...(state.sourceMode === 'local' ? [] : state.stock.filter(asset => state.categories.has(asset.category))), ...(state.sourceMode === 'stock' ? [] : state.local)];

function buttons() {
  const available = !!state.reference && !state.importing && state.ready;
  $('rerollButton').disabled = !available;
  $('refineButton').disabled = !available || state.fitting || !state.composition?.entries.length || state.settings.grid || state.composition.entries.length >= 8000;
  $('stopButton').hidden = !state.fitting && !state.importing;
  $('exportButton').disabled = !state.composition?.entries.length || state.fitting || state.importing;
  $('playButton').disabled = !state.composition?.entries.length || state.fitting;
  $('playButton').textContent = state.paused ? 'play' : 'pause';
  $('playButton').setAttribute('aria-label', state.paused ? 'Play animation' : 'Pause animation');
  $('photoSurface').setAttribute('aria-busy', String(state.fitting || state.importing || (!!preview && !previewReady)));
}
function savePreferences() {
  try { localStorage.setItem('photo-settings-v1', JSON.stringify({ settings: state.settings, seed: state.seed, categories: [...state.categories] })); } catch { /* Private browsing/storage pressure must not stop drawing. */ }
}
let preferences;
try { preferences = JSON.parse(localStorage.getItem('photo-settings-v1')); } catch { /* Start with defaults. */ }
if (preferences) { state.settings = normalizeSettings(preferences.settings); state.seed = Number(preferences.seed) >>> 0; }

const sliderGroups = {
  primarySliders: [
    ['resemblance', 'resemblance', 0, 100, 1, '%', 'loose color regions', 'fine detail'],
    ['count', 'image budget', 25, 8000, 25, '', 'sparse', 'dense'],
    ['size', 'image size', 1, 40, 1, '%', 'small', 'large']
  ],
  placementSliders: [
    ['variation', 'size variation', 0, 100, 1, '%'], ['overlap', 'overlap', 0, 100, 1, '%'],
    ['scatter', 'scatter', 0, 100, 1, '%'], ['rotation', 'rotation', 0, 180, 1, '°'],
    ['spill', 'spill across edges', 0, 100, 1, '%'], ['variety', 'asset variety', 0, 100, 1, '%']
  ],
  appearanceSliders: [['recolor', 'recolor allowance', 0, 100, 1, '%'], ['transparency', 'transparency allowance', 0, 100, 1, '%']]
};
for (const [group, sliders] of Object.entries(sliderGroups)) for (const [key, label, min, max, step, unit, low, high] of sliders) {
  const wrapper = document.createElement('div'); wrapper.className = 'photo-slider';
  wrapper.innerHTML = `<div class="control-label-row"><label for="photo-${key}">${label}</label><output id="value-${key}" for="photo-${key}"></output></div><input type="range" id="photo-${key}" min="${min}" max="${max}" step="${step}">${low ? `<div class="slider-extremes"><span>${low}</span><span>${high}</span></div>` : ''}`;
  $(group).append(wrapper);
  $(`photo-${key}`).addEventListener('input', () => {
    state.settings[key] = Number($(`photo-${key}`).value); $(`value-${key}`).textContent = state.settings[key] + unit;
    pressed('photoPresets', ''); scheduleFit();
  });
}
function syncSettings() {
  for (const sliders of Object.values(sliderGroups)) for (const [key, , , , , unit] of sliders) {
    $(`photo-${key}`).value = state.settings[key]; $(`value-${key}`).textContent = state.settings[key] + unit;
    $(`photo-${key}`).disabled = state.settings.grid && ['size', 'variation', 'overlap', 'scatter', 'rotation', 'spill'].includes(key);
  }
  $('gridMode').checked = state.settings.grid;
  $('photoSeed').value = state.seed.toString(16).padStart(8, '0');
}
syncSettings();
if (preferences) pressed('photoPresets', '');

function sizeStage() {
  const mobile = innerWidth <= 760, collapsed = document.body.classList.contains('controls-collapsed');
  const availableWidth = Math.max(120, innerWidth - (mobile ? 36 : collapsed ? 64 : 412));
  const availableHeight = Math.max(160, mobile ? Math.min(520, innerHeight * .53) : innerHeight - 150);
  const ratio = state.reference ? state.reference.width / state.reference.height : 1.2;
  const width = Math.floor(Math.min(availableWidth, availableHeight * ratio)), height = Math.floor(width / ratio);
  $('photoFrame').style.width = `${width + 2}px`;
  $('photoSurface').style.height = `${height + 2}px`;
}
window.addEventListener('resize', sizeStage); sizeStage();
function drawBitmap(bitmap) {
  try {
    const canvas = $('photoCanvas');
    if (canvas.width !== bitmap.width || canvas.height !== bitmap.height) { canvas.width = bitmap.width; canvas.height = bitmap.height; }
    context.drawImage(bitmap, 0, 0);
  } finally { bitmap.close(); }
}
function stopPreview() {
  state.previewId++; clearTimeout(previewTimer); preview?.close(); preview = null; previewReady = false;
  $('photoLowFps').hidden = true;
}
async function startPreview() {
  stopPreview();
  if (!state.composition || state.fitting || state.importing || state.exporting || state.suspended) return;
  const token = state.previewId, composition = state.composition;
  const scale = Math.min(1, 900 / Math.max(composition.referenceWidth, composition.referenceHeight));
  $('photoSpinner').hidden = false;
  const caption = `${composition.entries.length.toLocaleString()} images · ${new Set(composition.entries.map(entry => entry.assetId)).size} samples`;
  const session = new RasterSession({ progress: message => {
    if (token === state.previewId && message.phase === 'assets') $('photoMeta').textContent = `loading samples ${message.completed}/${message.total}`;
  } }); preview = session; buttons();
  let lastTime = performance.now(), first = true, average = 0;
  const animated = composition.entries.some(entry => state.catalog.get(entry.assetId)?.frames > 1);
  async function frame() {
    if (token !== state.previewId) return;
    const now = performance.now(), playing = !state.paused && $('animatePreview').checked && !$('showReference').checked && !document.hidden && !$('exportDialog').open;
    if (!first && (!playing || !animated)) { lastTime = now; previewTimer = setTimeout(frame, 120); return; }
    if (!first && playing) state.timeMs += now - lastTime;
    lastTime = now;
    const start = performance.now();
    try {
      const requestedTimeMs = state.timeMs;
      const output = await session.frame(requestedTimeMs);
      if (token !== state.previewId) { output.bitmap?.close(); return; }
      drawBitmap(output.bitmap); previewReady = true; first = false; state.displayedTimeMs = requestedTimeMs;
      $('photoMeta').textContent = caption;
      $('photoSpinner').hidden = true;
      average = average ? average * .8 + (performance.now() - start) * .2 : performance.now() - start;
      $('photoLowFps').hidden = !playing || !animated || average < 65;
      buttons();
      previewTimer = setTimeout(frame, Math.max(8, 1000 / 30 - (performance.now() - start)));
    } catch (error) {
      if (token !== state.previewId || error.name === 'AbortError') return;
      stopPreview(); $('photoSpinner').hidden = true; buttons();
      status(`Preview paused: ${error.message} The composition is still available to export.`, true);
    }
  }
  try {
    const result = await session.prepare(createScene(composition, state.catalog, Math.max(1, Math.round(composition.referenceWidth * scale)), Math.max(1, Math.round(composition.referenceHeight * scale)), { quality: false }));
    if (token !== state.previewId) return;
    if (result.skippedAssets?.length) status(`${composition.entries.length} images placed · ${result.skippedAssets.length} unavailable sources skipped`);
    await frame();
  } catch (error) {
    if (token !== state.previewId || error.name === 'AbortError') return;
    stopPreview(); $('photoSpinner').hidden = true; buttons(); status(`Preview unavailable: ${error.message}`, true);
  }
}
function scheduleFit() {
  savePreferences(); clearTimeout(fitTimer);
  if (state.fitting) { worker.postMessage({ type: 'cancel' }); state.fitId++; state.fitting = false; }
  stopPreview();
  if (state.reference && !state.importing) fitTimer = setTimeout(() => generate(), 300);
  buttons();
}
function generate(refine = false) {
  clearTimeout(fitTimer);
  if (!state.reference || !state.ready || state.importing) return;
  if (!selectedAssets().length) { stop(); status('Choose at least one stock category or add images from a folder.', true); return; }
  worker.postMessage({ type: 'cancel' }); stopPreview();
  const id = ++state.fitId, previous = state.composition;
  state.fitting = true; state.timeMs = 0; state.displayedTimeMs = 0; previousProgress = null;
  $('fitProgress').hidden = false; $('fitProgress').value = 0; $('photoSpinner').hidden = false;
  $('photoEmpty').hidden = true; $('showReference').checked = false; $('photoOriginal').hidden = true;
  $('photoCanvas').setAttribute('aria-label', `Collage reconstructed from ${state.reference.name}`);
  const settings = { ...state.settings };
  if (refine && previous) settings.count = Math.min(8000, previous.entries.length + Math.max(100, Math.round(previous.entries.length * .35)));
  const longest = settings.resemblance >= 80 ? 288 : 224;
  const scale = Math.min(1, longest / Math.max(state.reference.width, state.reference.height));
  const width = Math.max(1, Math.round(state.reference.width * scale)), height = Math.max(1, Math.round(state.reference.height * scale));
  const canvas = new OffscreenCanvas(width, height), ctx = canvas.getContext('2d', { willReadFrequently: true });
  ctx.fillStyle = '#fff'; ctx.fillRect(0, 0, width, height); ctx.drawImage(state.reference.bitmap, 0, 0, width, height);
  const pixels = ctx.getImageData(0, 0, width, height).data;
  status(refine ? 'refining the remaining differences…' : 'matching images…'); buttons();
  worker.postMessage({ type: 'fit', id, width, height, pixels, settings, seed: state.seed,
    categories: [...state.categories], sourceMode: state.sourceMode,
    initial: refine ? previous?.entries || [] : [], background: refine ? previous?.background : undefined }, [pixels.buffer]);
}
function completeFit(result, stopped = false) {
  state.fitting = false; $('fitProgress').hidden = true; $('photoSpinner').hidden = true;
  if (result?.entries?.length) {
    const { bitmap, ...data } = result;
    state.composition = { seed: state.seed, settings: { ...state.settings }, ...data, referenceWidth: state.reference.width, referenceHeight: state.reference.height };
    $('photoMeta').textContent = `${result.entries.length.toLocaleString()} images · ${new Set(result.entries.map(entry => entry.assetId)).size} samples`;
    status(`${stopped ? 'stopped · ' : ''}${result.entries.length.toLocaleString()} images placed${state.settings.grid ? ' on a grid' : ''}`);
    startPreview();
  } else { state.composition = null; status('No usable placements. Try larger images, more recoloring, or different samples.', true); }
  buttons();
}
function stop() {
  clearTimeout(fitTimer); worker?.postMessage({ type: 'cancel' }); state.fitId++; state.importId++;
  if (state.importing) {
    for (const item of pendingLocal) URL.revokeObjectURL(item.source);
    pendingLocal = []; state.importing = false; $('importProgress').hidden = true;
    $('localStatus').textContent = `import cancelled · ${state.local.length} previous images kept`;
  }
  if (state.fitting) completeFit(previousProgress, true);
  else { $('photoSpinner').hidden = true; buttons(); }
}

async function loadReference(file) {
  if (!file) return;
  const token = ++state.referenceId;
  let bitmap;
  try {
    if (file.size > 64 * 1024 * 1024) throw new Error('Choose a reference smaller than 64 MB.');
    bitmap = await createImageBitmap(file);
    if (bitmap.width * bitmap.height > 32e6) throw new Error('Choose a reference smaller than 32 megapixels.');
    if (token !== state.referenceId) { bitmap.close(); return; }
    stop(); stopPreview(); state.reference?.bitmap.close();
    if (referenceURL) URL.revokeObjectURL(referenceURL);
    referenceURL = URL.createObjectURL(file);
    state.reference = { bitmap, width: bitmap.width, height: bitmap.height, name: file.name };
    state.composition = null;
    $('photoOriginal').src = $('referenceThumbnail').src = referenceURL;
    $('referenceThumbnail').hidden = false; $('referenceName').textContent = file.name;
    $('photoTitle').textContent = file.name; $('photoDimensions').textContent = `${bitmap.width} × ${bitmap.height}`;
    $('showReference').disabled = false;
    $('exportWidth').value = Math.max(64, Math.min(1600, bitmap.width));
    sizeStage(); buttons(); generate();
  } catch (error) { bitmap?.close(); if (token === state.referenceId) status(`Could not open this reference. ${error.message}`, true); }
}
async function importFiles(fileList) {
  const files = Array.from(fileList).filter(file => /\.(gif|png|jpe?g|webp)$/i.test(file.name));
  if (!files.length) { status('Choose GIF, PNG, JPEG, or WebP images.', true); return; }
  stop(); stopPreview();
  state.importing = true; const id = ++state.importId;
  // Files are read sequentially in the worker. The main thread retains only
  // their Blob URLs, allowing the sidebar to stay interactive during analysis.
  pendingLocal = files.map((file, index) => ({ file, id: `local:${id}:${index}`, source: URL.createObjectURL(file) }));
  $('importProgress').hidden = false; $('importProgress').value = 0; $('photoSpinner').hidden = false;
  $('localStatus').textContent = `analyzing ${files.length} images…`; buttons();
  worker.postMessage({ type: 'import', id: `import:${id}`, items: pendingLocal });
}
function updateSources() {
  $('stockOptions').hidden = state.sourceMode === 'local'; $('localOptions').hidden = state.sourceMode === 'stock';
  pressed('sourceMode', state.sourceMode); $('assetCount').textContent = `${selectedAssets().length.toLocaleString()} available`;
}

try {
  worker = new Worker(new URL('./match-worker.js?v=20261009-photo-v1', import.meta.url), { type: 'module' });
  worker.onmessage = ({ data }) => {
    if (data.type === 'catalog') {
      state.stock = data.assets.map(asset => ({ ...asset, url: sourceURL(asset.source) }));
      for (const asset of state.stock) state.catalog.set(asset.id, asset);
      const categories = [...new Set(state.stock.map(asset => asset.category))].sort();
      state.categories = new Set(Array.isArray(preferences?.categories) ? preferences.categories.filter(category => categories.includes(category)) : categories);
      for (const category of categories) {
        const label = document.createElement('label'); label.className = 'check-row';
        const input = document.createElement('input'); input.type = 'checkbox'; input.checked = state.categories.has(category); input.value = category;
        const text = document.createElement('span'); text.textContent = category;
        label.append(input, text); $('categoryList').append(label);
        input.addEventListener('change', () => { if (input.checked) state.categories.add(category); else state.categories.delete(category); updateSources(); scheduleFit(); });
      }
      state.ready = true; updateSources(); buttons(); if (state.reference) generate();
    } else if (data.type === 'import-progress' && data.id === `import:${state.importId}`) {
      $('importProgress').value = data.completed / data.total;
      $('localStatus').textContent = `analyzing ${data.completed}/${data.total} images`;
    } else if (data.type === 'imported' && data.id === `import:${state.importId}`) {
      worker.postMessage({ type: 'commit-import', id: data.id });
      const accepted = new Set(data.assets.map(asset => asset.id));
      for (const asset of state.local) { state.catalog.delete(asset.id); URL.revokeObjectURL(asset.url); }
      for (const item of pendingLocal) if (!accepted.has(item.id)) URL.revokeObjectURL(item.source);
      pendingLocal = []; state.local = data.assets.map(asset => ({ ...asset, url: asset.source }));
      for (const asset of state.local) state.catalog.set(asset.id, asset);
      state.importing = false; state.composition = null;
      $('importProgress').hidden = true; $('photoSpinner').hidden = true;
      $('localStatus').textContent = `${data.assets.length} images ready${data.failures.length ? ` · ${data.failures.length} unreadable or oversized files skipped` : ''}`;
      updateSources(); buttons(); generate();
    } else if (data.type === 'error') {
      if (data.id === 'init') { state.ready = true; $('assetCount').textContent = 'stock unavailable'; buttons(); status(`${data.message} You can still use a local folder.`, true); }
      else if (data.id === state.fitId) { state.fitting = false; $('fitProgress').hidden = true; $('photoSpinner').hidden = true; buttons(); status(data.message, true); }
      else if (data.id === `import:${state.importId}`) { stop(); status(data.message, true); }
    } else if (data.type === 'progress' || data.type === 'fitted') {
      if (data.id !== state.fitId || !state.fitting) { data.bitmap?.close(); return; }
      if (data.bitmap) drawBitmap(data.bitmap);
      previousProgress = data;
      $('fitProgress').value = data.fraction ?? 1;
      $('photoMeta').textContent = `${data.entries.length.toLocaleString()} images · matching ${Math.round((data.fraction ?? 1) * 100)}%`;
      if (data.type === 'fitted') completeFit(data);
    }
  };
  worker.onerror = () => { stop(); state.ready = false; buttons(); status('The matching worker stopped. Reload this page to try again.', true); };
  worker.postMessage({ type: 'init', id: 'init' });
} catch { status('This page needs a browser with worker canvas support, such as current Chrome, Edge, Firefox, or Safari.', true); }

for (const id of ['chooseReference', 'photoEmpty']) $(id).onclick = () => $('referenceInput').click();
$('referenceInput').onchange = event => { loadReference(event.target.files[0]); event.target.value = ''; };
$('chooseFolder').onclick = () => $('folderInput').click(); $('chooseFiles').onclick = () => $('assetsInput').click();
for (const id of ['folderInput', 'assetsInput']) $(id).onchange = event => { importFiles(event.target.files); event.target.value = ''; };
for (const name of ['dragenter', 'dragover']) $('photoSurface').addEventListener(name, event => { event.preventDefault(); $('photoSurface').classList.add('is-dragging'); });
$('photoSurface').addEventListener('dragleave', () => $('photoSurface').classList.remove('is-dragging'));
$('photoSurface').addEventListener('drop', event => { event.preventDefault(); $('photoSurface').classList.remove('is-dragging'); loadReference(event.dataTransfer.files[0]); });
$('showReference').onchange = () => { $('photoOriginal').hidden = !$('showReference').checked; };
$('sourceMode').onclick = event => { const button = event.target.closest('button'); if (button) { state.sourceMode = button.value; updateSources(); scheduleFit(); } };
for (const [id, checked] of [['selectAllCategories', true], ['selectNoCategories', false]]) $(id).onclick = () => {
  for (const input of $('categoryList').querySelectorAll('input')) { input.checked = checked; if (checked) state.categories.add(input.value); else state.categories.delete(input.value); }
  updateSources(); scheduleFit();
};
$('photoPresets').onclick = event => { const button = event.target.closest('button'); if (button) { state.settings = { ...PRESETS[button.value] }; pressed('photoPresets', button.value); syncSettings(); scheduleFit(); } };
$('gridMode').onchange = () => { state.settings.grid = $('gridMode').checked; syncSettings(); pressed('photoPresets', ''); scheduleFit(); };
$('photoSeed').onchange = () => { if (/^[0-9a-f]{1,8}$/i.test($('photoSeed').value)) { state.seed = parseInt($('photoSeed').value, 16) >>> 0; scheduleFit(); } syncSettings(); };
$('rerollButton').onclick = () => { state.seed = crypto.getRandomValues(new Uint32Array(1))[0]; syncSettings(); savePreferences(); generate(); };
$('refineButton').onclick = () => generate(true); $('stopButton').onclick = stop;
$('playButton').onclick = () => { state.paused = !state.paused; buttons(); };
$('sidebarToggleButton').onclick = () => {
  const collapsed = document.body.classList.toggle('controls-collapsed');
  $('sidebarToggleButton').setAttribute('aria-expanded', String(!collapsed)); $('sidebarToggleButton').setAttribute('aria-label', collapsed ? 'Show controls' : 'Hide controls');
  $('sidebarToggleButton').textContent = collapsed ? '‹' : '›'; sizeStage();
};
document.addEventListener('keydown', event => {
  if ($('exportDialog').open || /INPUT|TEXTAREA|BUTTON|SELECT/.test(event.target.tagName) || event.ctrlKey || event.metaKey || event.altKey) return;
  if (event.key.toLowerCase() === 'r' && !$('rerollButton').disabled) $('rerollButton').click();
  if (event.code === 'Space' && !$('playButton').disabled) { event.preventDefault(); $('playButton').click(); }
});

$('exportButton').onclick = () => { exportStatus(''); $('exportDialog').showModal(); };
$('closeExport').onclick = () => { if (!state.exporting) $('exportDialog').close(); };
$('exportDialog').addEventListener('cancel', event => { if (state.exporting) { event.preventDefault(); exportAbort?.abort(); } });
$('exportDuration').oninput = () => { $('durationValue').textContent = `${$('exportDuration').value} sec`; };
$('exportFormat').onclick = event => {
  const button = event.target.closest('button'); if (!button) return;
  state.format = button.value; pressed('exportFormat', state.format); $('durationOptions').hidden = state.format === 'png'; $('startExport').textContent = `export ${state.format}`;
};
$('chooseExportFolder').onclick = async () => {
  if (!window.showDirectoryPicker) { exportStatus('This browser uses its download settings. Enable “Ask where to save each file” there to choose a folder.'); return; }
  try { folderHandle = await showDirectoryPicker({ mode: 'readwrite', startIn: 'downloads' }); $('exportDestination').textContent = folderHandle.name; }
  catch (error) { if (error.name !== 'AbortError') exportStatus(error.message, true); }
};
async function download(blob, name) {
  if (folderHandle) {
    const dot = name.lastIndexOf('.'), base = name.slice(0, dot), extension = name.slice(dot);
    for (let index = 1; ; index++) {
      try { await folderHandle.getFileHandle(name); name = `${base}-${index}${extension}`; }
      catch (error) { if (error.name === 'NotFoundError') break; throw error; }
    }
    const handle = await folderHandle.getFileHandle(name, { create: true }), stream = await handle.createWritable();
    try { await stream.write(blob); await stream.close(); } catch (error) { await stream.abort().catch(() => {}); throw error; }
  } else {
    const url = URL.createObjectURL(blob), link = document.createElement('a'); link.href = url; link.download = name; link.click(); setTimeout(() => URL.revokeObjectURL(url), 60000);
  }
}
$('cancelExport').onclick = () => exportAbort?.abort();
async function exportComposition(options = {}) {
  if (!state.composition?.entries.length || state.fitting || state.importing || state.exporting) throw new Error('Finish a composition before exporting.');
  state.exporting = true; stopPreview(); exportAbort = new AbortController();
  const composition = state.composition, catalog = new Map(state.catalog), format = options.format || state.format;
  $('exportSettings').disabled = true; $('startExport').disabled = true; $('closeExport').disabled = true; $('cancelExport').hidden = false;
  $('exportProgress').hidden = false; $('exportProgress').value = 0;
  try {
    const result = await renderExport(composition, catalog, { width: Number($('exportWidth').value), seconds: Number($('exportDuration').value), timeMs: state.displayedTimeMs,
      ...options, format, signal: exportAbort.signal, progress: ({ fraction, text }) => { $('exportProgress').value = fraction; exportStatus(text); options.progress?.({ fraction, text }); } });
    if (exportAbort.signal.aborted) throw new DOMException('Cancelled', 'AbortError');
    if (options.download !== false) {
      const base = state.reference.name.replace(/\.[^.]+$/, '').replace(/[^a-zA-Z0-9_-]+/g, '-').slice(0, 70) || 'photo';
      await download(result.blob, `${base}-collage-${composition.seed.toString(16)}.${format}`);
    }
    exportStatus(`${options.download === false ? 'ready' : 'saved'}${result.skipped ? ` · ${result.skipped} unavailable sources skipped` : ''}`);
    return result;
  } catch (error) { exportStatus(error.name === 'AbortError' ? 'export cancelled' : error.message, error.name !== 'AbortError'); throw error; }
  finally {
    state.exporting = false; exportAbort = null; $('exportSettings').disabled = false; $('startExport').disabled = false; $('closeExport').disabled = false;
    $('cancelExport').hidden = true; $('exportProgress').hidden = true; startPreview();
  }
}
$('startExport').onclick = () => { exportComposition().catch(() => {}); };
window.addEventListener('pagehide', event => {
  state.suspended = true; stop(); stopPreview(); exportAbort?.abort();
  if (!event.persisted) worker?.terminate();
});
window.addEventListener('pageshow', event => {
  state.suspended = false;
  if (event.persisted) startPreview();
});
// Small automation surface, matching the other tools. No source image data or
// local file handles are persisted or sent to a server.
window.PhotoApp = {
  getSummary: () => ({ ready: state.ready, fitting: state.fitting, importing: state.importing, exporting: state.exporting, previewReady,
    count: state.composition?.entries.length || 0, assets: selectedAssets().length, localAssets: state.local.length,
    seed: state.seed, settings: { ...state.settings }, error: state.composition?.error, baseError: state.composition?.baseError }),
  getComposition: () => state.composition ? structuredClone(state.composition) : null,
  export: exportComposition
};
