const MAX_VISIBLE_STAMPS = 25000;
const ALLOWED_EXTENSIONS = /\.(png|jpe?g|webp|gif)$/i;
const SESSION_STORAGE_KEY = "random-brush-drawer-session-v1";
const SESSION_STORAGE_POINTER_KEY = `${SESSION_STORAGE_KEY}-pointer`;
const SESSION_STORAGE_TAB_ID_KEY = `${SESSION_STORAGE_KEY}-tab-id`;
const SESSION_IDB_PREFIX = "idb:";
const SESSION_IDB_NAME = "image-brush-session-cache";
const SESSION_IDB_STORE_NAME = "snapshots";
const SAVE_DEBOUNCE_MS = 140;

const viewport = document.getElementById("viewport");
const world = document.getElementById("world");
const controlsPanel = document.getElementById("controls");
const sidebarToggleButton = document.getElementById("sidebarToggleButton");
const dropZone = document.getElementById("dropZone");
const dropZonePrompt = document.getElementById("dropZonePrompt");
const brushGallery = document.getElementById("brushGallery");
const brushInput = document.getElementById("brushInput");
const brushStatus = document.getElementById("brushStatus");
const sizeScaleGroup = document.getElementById("sizeScaleGroup");
const sizeSlider = document.getElementById("sizeSlider");
const sizeValue = document.getElementById("sizeValue");
const consistentToggle = document.getElementById("consistentToggle");
const consistentSizeGroup = document.getElementById("consistentSizeGroup");
const consistentSizeSlider = document.getElementById("consistentSizeSlider");
const consistentSizeValue = document.getElementById("consistentSizeValue");
const spacingSlider = document.getElementById("spacingSlider");
const spacingValue = document.getElementById("spacingValue");
const rotationSlider = document.getElementById("rotationSlider");
const rotationValue = document.getElementById("rotationValue");
const rotationIndicator = document.getElementById("rotationIndicator");
const rotationNeedle = document.getElementById("rotationNeedle");
const opacitySlider = document.getElementById("opacitySlider");
const opacityValue = document.getElementById("opacityValue");
const renderModeToggle = document.getElementById("renderModeToggle");
const renderModeLabel = document.getElementById("renderModeLabel");
const cursorTrailToggle = document.getElementById("cursorTrailToggle");
const cursorTrailCountGroup = document.getElementById("cursorTrailCountGroup");
const cursorTrailCountSlider = document.getElementById("cursorTrailCountSlider");
const cursorTrailCountValue = document.getElementById("cursorTrailCountValue");
const eraseCursor = document.getElementById("eraseCursor");
const eraseModeButton = document.getElementById("eraseModeButton");
const undoButton = document.getElementById("undoButton");
const redoButton = document.getElementById("redoButton");
const clearButton = document.getElementById("clearButton");
const clearConfirmModal = document.getElementById("clearConfirmModal");
const confirmYesButton = document.getElementById("confirmYesButton");
const confirmNoButton = document.getElementById("confirmNoButton");

const LOW_WEIGHT_MULTIPLIER = 0.12;
const HIGH_WEIGHT_MULTIPLIER = 4.5;
const ERASER_PERCENT_SIZE_MULTIPLIER = 2;
const ERASER_GLOBAL_SIZE_MULTIPLIER = 2.5;
const MIN_CAMERA_SCALE = 0.03;
const MAX_CAMERA_SCALE = 6;
const CURSOR_TRAIL_FADE_MS = 4000;

const state = {
  brushes: [],
  strokes: [],
  history: [],
  redoHistory: [],
  camera: { x: 0, y: 0, scale: 1 },
  drawing: null,
  erasing: null,
  panning: null,
  strokeById: new Map(),
  urlRefCounts: new Map(),
  nextBrushId: 1,
  nextStrokeId: 1,
  saveTimerId: null,
  soloBrushId: null,
  sidebarCollapsed: false,
  eraseMode: false,
  pointerInViewport: false,
  lastPointerClientX: 0,
  lastPointerClientY: 0,
  cursorTrailEntries: [],
  cursorTrailLastWorldX: null,
  cursorTrailLastWorldY: null
};

let snapshotDbPromise = null;
let sessionTabIdCache = null;

function clamp(value, min, max) {
  return Math.min(max, Math.max(min, value));
}

function parseNumericInputValue(input, fallback) {
  const numericValue = Number(input.value);
  if (!Number.isFinite(numericValue)) {
    return fallback;
  }
  return numericValue;
}

function setInputNumericValue(input, nextValue) {
  const min = Number(input.min);
  const max = Number(input.max);
  let numericValue = Number(nextValue);
  if (!Number.isFinite(numericValue)) {
    return;
  }
  if (Number.isFinite(min)) {
    numericValue = Math.max(min, numericValue);
  }
  if (Number.isFinite(max)) {
    numericValue = Math.min(max, numericValue);
  }
  input.value = String(numericValue);
}

function createSessionId() {
  if (typeof crypto !== "undefined" && typeof crypto.randomUUID === "function") {
    return crypto.randomUUID();
  }
  return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 10)}`;
}

function getSessionTabId() {
  if (sessionTabIdCache) {
    return sessionTabIdCache;
  }

  let tabId = "";
  try {
    tabId = sessionStorage.getItem(SESSION_STORAGE_TAB_ID_KEY) || "";
    if (!tabId) {
      tabId = createSessionId();
      sessionStorage.setItem(SESSION_STORAGE_TAB_ID_KEY, tabId);
    }
  } catch (error) {
    tabId = createSessionId();
  }

  sessionTabIdCache = tabId;
  return sessionTabIdCache;
}

function openSnapshotDb() {
  if (snapshotDbPromise) {
    return snapshotDbPromise;
  }

  snapshotDbPromise = new Promise((resolve, reject) => {
    if (typeof indexedDB === "undefined") {
      reject(new Error("IndexedDB unavailable"));
      return;
    }

    const request = indexedDB.open(SESSION_IDB_NAME, 1);
    request.onupgradeneeded = () => {
      const database = request.result;
      if (!database.objectStoreNames.contains(SESSION_IDB_STORE_NAME)) {
        database.createObjectStore(SESSION_IDB_STORE_NAME);
      }
    };
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error || new Error("Failed to open snapshot DB"));
  });

  return snapshotDbPromise;
}

async function writeSnapshotToIndexedDb(tabId, snapshotJson) {
  const database = await openSnapshotDb();
  await new Promise((resolve, reject) => {
    const transaction = database.transaction(SESSION_IDB_STORE_NAME, "readwrite");
    transaction.objectStore(SESSION_IDB_STORE_NAME).put(snapshotJson, tabId);
    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error || new Error("Snapshot write failed"));
    transaction.onabort = () => reject(transaction.error || new Error("Snapshot write aborted"));
  });
}

async function readSnapshotFromIndexedDb(tabId) {
  const database = await openSnapshotDb();
  return new Promise((resolve, reject) => {
    const transaction = database.transaction(SESSION_IDB_STORE_NAME, "readonly");
    const request = transaction.objectStore(SESSION_IDB_STORE_NAME).get(tabId);
    request.onsuccess = () => resolve(typeof request.result === "string" ? request.result : null);
    request.onerror = () => reject(request.error || new Error("Snapshot read failed"));
  });
}

function getSessionStorageItemSafe(key) {
  try {
    return sessionStorage.getItem(key);
  } catch (error) {
    return null;
  }
}

function setSessionStorageItemSafe(key, value) {
  try {
    sessionStorage.setItem(key, value);
    return true;
  } catch (error) {
    return false;
  }
}

function removeSessionStorageItemSafe(key) {
  try {
    sessionStorage.removeItem(key);
  } catch (error) {
    // Ignore storage access errors.
  }
}

function isBlobUrl(url) {
  return typeof url === "string" && url.startsWith("blob:");
}

function findBrushById(id) {
  return state.brushes.find((brush) => brush.id === id) || null;
}

function getSoloBrush() {
  if (!Number.isFinite(Number(state.soloBrushId))) {
    return null;
  }
  const brush = findBrushById(Number(state.soloBrushId));
  if (!brush) {
    state.soloBrushId = null;
    return null;
  }
  return brush;
}

function updateSliderText() {
  sizeValue.textContent = String(sizeSlider.value);
  consistentSizeValue.textContent = String(consistentSizeSlider.value);
  spacingValue.textContent = String(spacingSlider.value);
  rotationValue.textContent = String(rotationSlider.value);
  opacityValue.textContent = String(opacitySlider.value);
  cursorTrailCountValue.textContent = String(cursorTrailCountSlider.value);
}

function updateConsistentModeUI() {
  const isConsistentMode = consistentToggle.checked;
  sizeSlider.disabled = isConsistentMode;
  sizeScaleGroup.classList.toggle("is-disabled", isConsistentMode);
  consistentSizeGroup.hidden = !isConsistentMode;
  consistentSizeSlider.disabled = !isConsistentMode;
}

function updateRenderModeUI() {
  renderModeLabel.textContent = renderModeToggle.checked ? "linear" : "point";
}

function resetCursorTrailAnchor() {
  state.cursorTrailLastWorldX = null;
  state.cursorTrailLastWorldY = null;
}

function getCursorTrailLimit() {
  const requested = parseNumericInputValue(cursorTrailCountSlider, 24);
  return Math.max(1, Math.floor(requested));
}

function removeCursorTrailEntry(entry) {
  if (!entry || entry.removed) {
    return;
  }
  entry.removed = true;

  if (entry.timeoutId !== null) {
    window.clearTimeout(entry.timeoutId);
    entry.timeoutId = null;
  }

  const index = state.cursorTrailEntries.indexOf(entry);
  if (index >= 0) {
    state.cursorTrailEntries.splice(index, 1);
  }

  if (entry.element && entry.element.parentElement) {
    entry.element.remove();
  }
}

function clearCursorTrail() {
  const entries = state.cursorTrailEntries.slice();
  for (const entry of entries) {
    removeCursorTrailEntry(entry);
  }
  resetCursorTrailAnchor();
}

function enforceCursorTrailLimit() {
  const limit = getCursorTrailLimit();
  while (state.cursorTrailEntries.length > limit) {
    const oldest = state.cursorTrailEntries[0];
    if (!oldest) {
      break;
    }
    removeCursorTrailEntry(oldest);
  }
}

function updateCursorTrailUI() {
  const enabled = cursorTrailToggle.checked;
  cursorTrailCountGroup.hidden = !enabled;
  cursorTrailCountSlider.disabled = !enabled;
  cursorTrailCountGroup.classList.toggle("is-disabled", !enabled);

  if (!enabled) {
    clearCursorTrail();
    return;
  }

  enforceCursorTrailLimit();
}

function spawnCursorTrailStamp(worldX, worldY) {
  const limit = getCursorTrailLimit();
  while (state.cursorTrailEntries.length >= limit) {
    const oldest = state.cursorTrailEntries[0];
    if (!oldest) {
      break;
    }
    removeCursorTrailEntry(oldest);
  }

  const brush = pickRandomBrush();
  if (!brush) {
    return false;
  }

  let width = 0;
  let height = 0;
  if (consistentToggle.checked) {
    width = Math.max(4, Number(consistentSizeSlider.value));
    height = Math.max(4, width * (brush.height / brush.width));
  } else {
    const scale = Number(sizeSlider.value) / 100;
    width = Math.max(4, brush.width * scale);
    height = Math.max(4, brush.height * scale);
  }

  const trailStamp = document.createElement("img");
  trailStamp.className = "trail-stamp";
  trailStamp.src = brush.url;
  trailStamp.alt = "";
  trailStamp.draggable = false;
  trailStamp.style.width = `${width}px`;
  trailStamp.style.height = `${height}px`;
  trailStamp.style.left = `${worldX - width / 2}px`;
  trailStamp.style.top = `${worldY - height / 2}px`;
  const rotation = parseNumericInputValue(rotationSlider, 0);
  trailStamp.style.transform = `rotate(${rotation}deg)`;
  trailStamp.style.imageRendering = renderModeToggle.checked ? "auto" : "pixelated";
  const opacity = clamp(Number(opacitySlider.value) / 100, 0, 1);
  trailStamp.style.opacity = String(opacity);
  trailStamp.style.setProperty("--trail-start-opacity", String(opacity));
  world.appendChild(trailStamp);

  const entry = {
    element: trailStamp,
    timeoutId: null,
    removed: false
  };
  entry.timeoutId = window.setTimeout(() => {
    removeCursorTrailEntry(entry);
  }, CURSOR_TRAIL_FADE_MS);
  state.cursorTrailEntries.push(entry);
  return true;
}

function updateCursorTrailAtClientPoint(clientX, clientY) {
  if (!cursorTrailToggle.checked || state.eraseMode || state.panning || !state.pointerInViewport) {
    resetCursorTrailAnchor();
    return;
  }

  if (!state.brushes.length || !hasEnabledBrushes()) {
    resetCursorTrailAnchor();
    return;
  }

  const point = screenToWorld(clientX, clientY);
  const spacing = Math.max(1, parseNumericInputValue(spacingSlider, 48));
  if (
    !Number.isFinite(state.cursorTrailLastWorldX) ||
    !Number.isFinite(state.cursorTrailLastWorldY)
  ) {
    if (spawnCursorTrailStamp(point.x, point.y)) {
      state.cursorTrailLastWorldX = point.x;
      state.cursorTrailLastWorldY = point.y;
    } else {
      resetCursorTrailAnchor();
    }
    return;
  }

  const dx = point.x - state.cursorTrailLastWorldX;
  const dy = point.y - state.cursorTrailLastWorldY;
  const distance = Math.hypot(dx, dy);
  if (distance < spacing) {
    return;
  }

  const stepX = dx / distance;
  const stepY = dy / distance;
  let remaining = distance;
  let cursorX = state.cursorTrailLastWorldX;
  let cursorY = state.cursorTrailLastWorldY;

  while (remaining >= spacing) {
    cursorX += stepX * spacing;
    cursorY += stepY * spacing;
    if (!spawnCursorTrailStamp(cursorX, cursorY)) {
      resetCursorTrailAnchor();
      return;
    }
    remaining -= spacing;
  }

  state.cursorTrailLastWorldX = cursorX;
  state.cursorTrailLastWorldY = cursorY;
}

function updateSidebarVisibilityUI() {
  controlsPanel.classList.toggle("is-collapsed", state.sidebarCollapsed);
  sidebarToggleButton.setAttribute("aria-expanded", String(!state.sidebarCollapsed));
  sidebarToggleButton.setAttribute(
    "aria-label",
    state.sidebarCollapsed ? "Show sidebar contents" : "Hide sidebar contents"
  );
}

function updateRotationIndicator() {
  const angle = parseNumericInputValue(rotationSlider, 0);
  rotationNeedle.style.transform = `translate(-50%, -100%) rotate(${angle}deg)`;
}

function getEnabledBrushesForSizing() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    return [soloBrush];
  }
  const enabled = state.brushes.filter((brush) => brush.enabled);
  if (enabled.length) {
    return enabled;
  }
  return state.brushes;
}

function getCurrentEraserDiameterWorld() {
  if (consistentToggle.checked) {
    return Math.max(8, parseNumericInputValue(consistentSizeSlider, 96)) * ERASER_GLOBAL_SIZE_MULTIPLIER;
  }

  const scale = parseNumericInputValue(sizeSlider, 100) / 100;
  const brushesForSizing = getEnabledBrushesForSizing();
  if (!brushesForSizing.length) {
    return (
      Math.max(8, 96 * scale * ERASER_PERCENT_SIZE_MULTIPLIER) * ERASER_GLOBAL_SIZE_MULTIPLIER
    );
  }

  const totalWidth = brushesForSizing.reduce((sum, brush) => sum + brush.width, 0);
  const averageWidth = totalWidth / brushesForSizing.length;
  return (
    Math.max(8, averageWidth * scale * ERASER_PERCENT_SIZE_MULTIPLIER) * ERASER_GLOBAL_SIZE_MULTIPLIER
  );
}

function updateEraseCursorGeometry() {
  const diameterScreen = Math.max(8, getCurrentEraserDiameterWorld() * state.camera.scale);
  eraseCursor.style.width = `${diameterScreen}px`;
  eraseCursor.style.height = `${diameterScreen}px`;
  eraseCursor.style.marginLeft = `${-diameterScreen / 2}px`;
  eraseCursor.style.marginTop = `${-diameterScreen / 2}px`;
}

function updateEraseCursorPosition(clientX, clientY) {
  eraseCursor.style.left = `${clientX}px`;
  eraseCursor.style.top = `${clientY}px`;
}

function updateEraseCursorVisibility() {
  const shouldShow = state.eraseMode && state.pointerInViewport && !state.panning;
  eraseCursor.classList.toggle("is-visible", shouldShow);
}

function updateEraseModeUI() {
  eraseModeButton.classList.toggle("is-active", state.eraseMode);
  eraseModeButton.setAttribute("aria-pressed", String(state.eraseMode));
  viewport.classList.toggle("is-erasing", state.eraseMode);
  updateEraseCursorGeometry();
  updateEraseCursorVisibility();
}

function isStampAtLeastHalfInsideCircle(element, centerX, centerY, radius) {
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = parseFloat(element.style.width) || 0;
  const height = parseFloat(element.style.height) || 0;
  if (width <= 0 || height <= 0) {
    return false;
  }

  const centerStampX = left + width / 2;
  const centerStampY = top + height / 2;
  const halfDiagonal = Math.hypot(width, height) / 2;
  const centerDistance = Math.hypot(centerStampX - centerX, centerStampY - centerY);

  if (centerDistance > radius + halfDiagonal) {
    return false;
  }

  if (centerDistance + halfDiagonal <= radius) {
    return true;
  }

  const rotation = Number(element.dataset.rotation) || 0;
  const radians = (rotation * Math.PI) / 180;
  const cos = Math.cos(radians);
  const sin = Math.sin(radians);
  const gridSize = 8;
  const totalSamples = gridSize * gridSize;
  const threshold = Math.ceil(totalSamples * 0.5);
  let insideSamples = 0;

  for (let row = 0; row < gridSize; row += 1) {
    const localY = ((row + 0.5) / gridSize - 0.5) * height;
    for (let col = 0; col < gridSize; col += 1) {
      const localX = ((col + 0.5) / gridSize - 0.5) * width;
      const sampleX = centerStampX + localX * cos - localY * sin;
      const sampleY = centerStampY + localX * sin + localY * cos;
      if (Math.hypot(sampleX - centerX, sampleY - centerY) <= radius) {
        insideSamples += 1;
      }

      const samplesTaken = row * gridSize + col + 1;
      const samplesRemaining = totalSamples - samplesTaken;
      if (insideSamples >= threshold) {
        return true;
      }
      if (insideSamples + samplesRemaining < threshold) {
        return false;
      }
    }
  }

  return insideSamples >= threshold;
}

function removeStrokeFromState(stroke) {
  state.strokeById.delete(stroke.id);
  const strokeIndex = state.strokes.indexOf(stroke);
  if (strokeIndex >= 0) {
    state.strokes.splice(strokeIndex, 1);
  }
}

function removeStampElementFromState(element, removalContext = null) {
  const strokeId = Number(element.dataset.strokeId);
  const stroke = Number.isFinite(strokeId) ? state.strokeById.get(strokeId) : null;
  const strokeIndex = stroke ? state.strokes.indexOf(stroke) : -1;
  const stampIndex = stroke ? stroke.elements.indexOf(element) : -1;

  if (removalContext) {
    let worldIndex = -1;
    if (removalContext.worldOrder instanceof Map && removalContext.worldOrder.has(element)) {
      worldIndex = Number(removalContext.worldOrder.get(element));
    } else {
      worldIndex = Array.prototype.indexOf.call(world.children, element);
    }

    removalContext.records.push({
      element,
      stroke,
      strokeIndex,
      stampIndex,
      worldIndex
    });
  }

  if (stroke && stampIndex >= 0) {
    stroke.elements.splice(stampIndex, 1);
    if (!stroke.elements.length) {
      removeStrokeFromState(stroke);
    }
  }

  if (element.parentElement === world) {
    decrementUrlRef(element.dataset.brushUrl);
    element.remove();
  }
}

function eraseAtPoint(worldX, worldY, radiusWorld, removalContext = null) {
  let removedAny = false;
  const elements = Array.from(world.children);
  for (const element of elements) {
    if (!element.classList.contains("stamp")) {
      continue;
    }
    if (!isStampAtLeastHalfInsideCircle(element, worldX, worldY, radiusWorld)) {
      continue;
    }
    removeStampElementFromState(element, removalContext);
    removedAny = true;
  }
  return removedAny;
}

function eraseAlongPath(erasing, x, y) {
  const radiusWorld = getCurrentEraserDiameterWorld() / 2;
  const dx = x - erasing.lastX;
  const dy = y - erasing.lastY;
  const distance = Math.hypot(dx, dy);

  if (distance === 0) {
    if (eraseAtPoint(x, y, radiusWorld, erasing.removalContext)) {
      erasing.changed = true;
    }
    return;
  }

  const step = Math.max(3, radiusWorld * 0.35);
  const stepX = dx / distance;
  const stepY = dy / distance;
  let traveled = 0;

  while (traveled <= distance) {
    const sampleX = erasing.lastX + stepX * traveled;
    const sampleY = erasing.lastY + stepY * traveled;
    if (eraseAtPoint(sampleX, sampleY, radiusWorld, erasing.removalContext)) {
      erasing.changed = true;
    }
    traveled += step;
  }

  erasing.lastX = x;
  erasing.lastY = y;
}

function getVisibleStampCount() {
  return world.getElementsByClassName("stamp").length;
}

function notifyStampLimitReached() {
  updateBrushStatus(
    `Canvas limit reached (${MAX_VISIBLE_STAMPS.toLocaleString()} images). Undo or clear to add more.`
  );
}

function serializeStrokeList(strokes) {
  return strokes.map((stroke) => ({
    id: Number.isFinite(Number(stroke.id)) ? Number(stroke.id) : null,
    stamps: stroke.elements.map((element) => ({
      // Persist only layout/render metadata and brush linkage for compact reloads.
      brushId: Number(element.dataset.brushId) || null,
      left: parseFloat(element.style.left) || 0,
      top: parseFloat(element.style.top) || 0,
      width: parseFloat(element.style.width) || 0,
      height: parseFloat(element.style.height) || 0,
      rotation: Number(element.dataset.rotation) || 0,
      opacity: Number.isFinite(Number(element.style.opacity))
        ? clamp(Number(element.style.opacity), 0, 1)
        : 1,
      imageRendering: element.style.imageRendering === "auto" ? "auto" : "pixelated"
    }))
  }));
}

function getRedoDrawStrokes() {
  return state.redoHistory
    .filter((action) => action && action.type === "draw" && action.stroke)
    .map((action) => action.stroke);
}

function collectStrokeBrushSources() {
  const currentBrushIds = new Set(state.brushes.map((brush) => brush.id));
  const byId = new Map();
  const strokeLists = [state.strokes, getRedoDrawStrokes()];

  for (const strokeList of strokeLists) {
    for (const stroke of strokeList) {
      for (const element of stroke.elements) {
        const brushId = Number(element.dataset.brushId);
        if (!Number.isFinite(brushId) || currentBrushIds.has(brushId)) {
          continue;
        }

        if (byId.has(brushId)) {
          continue;
        }

        const brushUrl = element.dataset.brushUrl || element.getAttribute("src") || "";
        if (!brushUrl) {
          continue;
        }

        byId.set(brushId, {
          id: brushId,
          url: brushUrl,
          name: `brush-${brushId}`,
          width: Math.max(1, parseFloat(element.style.width) || 1),
          height: Math.max(1, parseFloat(element.style.height) || 1)
        });
      }
    }
  }

  return Array.from(byId.values());
}

function buildSessionSnapshot() {
  return {
    version: 1,
    soloBrushId: Number.isFinite(Number(state.soloBrushId))
      ? Number(state.soloBrushId)
      : null,
    camera: {
      x: state.camera.x,
      y: state.camera.y,
      scale: state.camera.scale
    },
    controls: {
      size: parseNumericInputValue(sizeSlider, 100),
      consistent: consistentToggle.checked,
      consistentSize: parseNumericInputValue(consistentSizeSlider, 96),
      spacing: parseNumericInputValue(spacingSlider, 48),
      rotation: parseNumericInputValue(rotationSlider, 0),
      opacity: parseNumericInputValue(opacitySlider, 100),
      renderLinear: renderModeToggle.checked,
      cursorTrailEnabled: cursorTrailToggle.checked,
      cursorTrailCount: parseNumericInputValue(cursorTrailCountSlider, 24),
      sidebarCollapsed: state.sidebarCollapsed
    },
    brushes: state.brushes.map((brush) => ({
      id: brush.id,
      url: brush.url,
      name: brush.name,
      width: brush.width,
      height: brush.height,
      enabled: brush.enabled,
      weightMode: brush.weightMode
    })),
    strokeBrushes: collectStrokeBrushSources(),
    strokes: serializeStrokeList(state.strokes),
    redoStrokes: serializeStrokeList(getRedoDrawStrokes())
  };
}

async function saveSessionStateNow() {
  const snapshot = buildSessionSnapshot();
  const snapshotJson = JSON.stringify(snapshot);

  try {
    sessionStorage.setItem(SESSION_STORAGE_KEY, snapshotJson);
    removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
  } catch (error) {
    const tabId = getSessionTabId();
    try {
      await writeSnapshotToIndexedDb(tabId, snapshotJson);
      removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
      setSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY, `${SESSION_IDB_PREFIX}${tabId}`);
    } catch (secondaryError) {
      // Ignore transient quota/storage issues and continue app runtime.
    }
  }
}

function scheduleSessionSave() {
  if (state.saveTimerId !== null) {
    return;
  }
  state.saveTimerId = window.setTimeout(() => {
    state.saveTimerId = null;
    void saveSessionStateNow();
  }, SAVE_DEBOUNCE_MS);
}

function flushSessionSaveNow() {
  if (state.saveTimerId !== null) {
    window.clearTimeout(state.saveTimerId);
    state.saveTimerId = null;
  }
  void saveSessionStateNow();
}

function createStampElement(stampData, brush) {
  const width = Math.max(1, Number(stampData.width) || brush.width);
  const height = Math.max(1, Number(stampData.height) || brush.height);
  const stamp = document.createElement("img");

  stamp.className = "stamp";
  stamp.src = brush.url;
  stamp.alt = "";
  stamp.draggable = false;
  stamp.dataset.brushUrl = brush.url;
  stamp.dataset.brushId = String(brush.id);
  stamp.style.width = `${width}px`;
  stamp.style.height = `${height}px`;
  stamp.style.left = `${Number(stampData.left) || 0}px`;
  stamp.style.top = `${Number(stampData.top) || 0}px`;
  const opacity = Number(stampData.opacity);
  const rotation = Number(stampData.rotation) || 0;
  stamp.dataset.rotation = String(rotation);
  stamp.style.opacity = String(Number.isFinite(opacity) ? clamp(opacity, 0, 1) : 1);
  stamp.style.imageRendering = stampData.imageRendering === "auto" ? "auto" : "pixelated";
  stamp.style.transform = `rotate(${rotation}deg)`;

  return stamp;
}

function resolveBrushForStamp(stampData, brushById) {
  const brushId = Number(stampData?.brushId);
  let brush = Number.isFinite(brushId) ? brushById.get(brushId) : null;
  if (!brush && typeof stampData?.url === "string") {
    brush = state.brushes.find((entry) => entry.url === stampData.url) || null;
  }
  return brush;
}

function restoreStrokeList(serializedStrokes, brushById, appendToWorld) {
  const restored = [];
  const list = Array.isArray(serializedStrokes) ? serializedStrokes : [];

  for (const strokeData of list) {
    const snapshotStrokeId = Number(strokeData?.id);
    const strokeId = Number.isFinite(snapshotStrokeId) ? snapshotStrokeId : state.nextStrokeId;
    const stroke = { id: strokeId, elements: [] };
    if (strokeId >= state.nextStrokeId) {
      state.nextStrokeId = strokeId + 1;
    }
    const stamps = Array.isArray(strokeData?.stamps) ? strokeData.stamps : [];
    for (const stampData of stamps) {
      const brush = resolveBrushForStamp(stampData, brushById);
      if (!brush) {
        continue;
      }

      const stamp = createStampElement(stampData, brush);
      stamp.dataset.strokeId = String(stroke.id);
      if (appendToWorld) {
        world.appendChild(stamp);
        incrementUrlRef(brush.url);
      }
      stroke.elements.push(stamp);
    }

    if (stroke.elements.length) {
      restored.push(stroke);
    }
  }

  return restored;
}

async function restoreSessionState() {
  let raw = getSessionStorageItemSafe(SESSION_STORAGE_KEY);
  if (!raw) {
    const pointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY) || "";
    if (pointer.startsWith(SESSION_IDB_PREFIX)) {
      const tabId = pointer.slice(SESSION_IDB_PREFIX.length);
      if (tabId) {
        try {
          raw = await readSnapshotFromIndexedDb(tabId);
        } catch (error) {
          raw = null;
        }
      }
    }
  }

  if (!raw) {
    return false;
  }

  try {
    const snapshot = JSON.parse(raw);
    if (!snapshot || snapshot.version !== 1) {
      return false;
    }

    const restoredBrushes = Array.isArray(snapshot.brushes) ? snapshot.brushes : [];
    state.brushes = restoredBrushes
      .filter((brush) => brush && typeof brush.url === "string" && Number.isFinite(Number(brush.id)))
      .map((brush) => ({
        id: Number(brush.id),
        url: brush.url,
        name: String(brush.name || "brush"),
        width: Math.max(1, Number(brush.width) || 1),
        height: Math.max(1, Number(brush.height) || 1),
        enabled: brush.enabled !== false,
        weightMode: brush.weightMode === "low" || brush.weightMode === "high" ? brush.weightMode : "normal"
      }));

    const snapshotSoloBrushId = Number(snapshot.soloBrushId);
    state.soloBrushId = Number.isFinite(snapshotSoloBrushId) ? snapshotSoloBrushId : null;
    const soloBrush = getSoloBrush();
    if (soloBrush) {
      soloBrush.enabled = true;
    }

    let maxBrushId = 0;
    for (const brush of state.brushes) {
      if (brush.id > maxBrushId) {
        maxBrushId = brush.id;
      }
    }
    state.nextBrushId = maxBrushId + 1;

    world.innerHTML = "";
    state.urlRefCounts.clear();
    state.strokes = [];
    state.history = [];
    state.redoHistory = [];
    state.cursorTrailEntries = [];
    resetCursorTrailAnchor();
    state.strokeById.clear();
    state.nextStrokeId = 1;

    const brushById = new Map(state.brushes.map((brush) => [brush.id, brush]));
    const restoredStrokeBrushes = Array.isArray(snapshot.strokeBrushes) ? snapshot.strokeBrushes : [];
    for (const source of restoredStrokeBrushes) {
      const sourceId = Number(source?.id);
      const sourceUrl = typeof source?.url === "string" ? source.url : "";
      if (!Number.isFinite(sourceId) || !sourceUrl || brushById.has(sourceId)) {
        continue;
      }
      brushById.set(sourceId, {
        id: sourceId,
        url: sourceUrl,
        name: String(source?.name || `brush-${sourceId}`),
        width: Math.max(1, Number(source?.width) || 1),
        height: Math.max(1, Number(source?.height) || 1),
        enabled: false,
        weightMode: "normal"
      });
    }

    state.strokes = restoreStrokeList(snapshot.strokes, brushById, true);
    const restoredRedoStrokes = restoreStrokeList(snapshot.redoStrokes, brushById, false);
    for (const stroke of state.strokes) {
      state.strokeById.set(stroke.id, stroke);
    }
    state.history = state.strokes.map((stroke) => ({ type: "draw", stroke }));
    state.redoHistory = restoredRedoStrokes.map((stroke) => ({ type: "draw", stroke }));

    const controls = snapshot.controls || {};
    setInputNumericValue(sizeSlider, controls.size);
    consistentToggle.checked = Boolean(controls.consistent);
    setInputNumericValue(consistentSizeSlider, controls.consistentSize);
    setInputNumericValue(spacingSlider, controls.spacing);
    setInputNumericValue(rotationSlider, controls.rotation);
    setInputNumericValue(opacitySlider, controls.opacity);
    renderModeToggle.checked = Boolean(controls.renderLinear);
    cursorTrailToggle.checked = Boolean(controls.cursorTrailEnabled);
    setInputNumericValue(cursorTrailCountSlider, controls.cursorTrailCount);
    state.sidebarCollapsed = Boolean(controls.sidebarCollapsed);

    const camera = snapshot.camera || {};
    if (Number.isFinite(Number(camera.x))) {
      state.camera.x = Number(camera.x);
    }
    if (Number.isFinite(Number(camera.y))) {
      state.camera.y = Number(camera.y);
    }
    if (Number.isFinite(Number(camera.scale))) {
      state.camera.scale = clamp(Number(camera.scale), MIN_CAMERA_SCALE, MAX_CAMERA_SCALE);
    }

    updateSliderText();
    updateConsistentModeUI();
    updateRenderModeUI();
    updateCursorTrailUI();
    updateRotationIndicator();
    updateSidebarVisibilityUI();
    updateEraseModeUI();
    updateUndoState();
    updateBrushStatus();
    renderBrushGallery();
    renderCamera();
    return true;
  } catch (error) {
    removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
    removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    return false;
  }
}

function updateUndoState() {
  const hasHistory = state.history.length > 0;
  const hasRedo = state.redoHistory.length > 0;
  undoButton.disabled = !hasHistory;
  redoButton.disabled = !hasRedo;
  clearButton.disabled = getVisibleStampCount() === 0;
}

function countEnabledBrushes() {
  let enabledCount = 0;
  for (const brush of state.brushes) {
    if (brush.enabled) {
      enabledCount += 1;
    }
  }
  return enabledCount;
}

function hasEnabledBrushes() {
  return countEnabledBrushes() > 0;
}

function updateBrushStatus(customMessage) {
  if (customMessage) {
    brushStatus.textContent = customMessage;
    return;
  }

  if (!state.brushes.length) {
    brushStatus.textContent = "No brush data loaded.";
    return;
  }

  const enabledCount = countEnabledBrushes();
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    brushStatus.textContent =
      `Loaded ${state.brushes.length} brush image(s). Solo: ${soloBrush.name}.`;
    return;
  }

  if (enabledCount === 0) {
    brushStatus.textContent =
      `Loaded ${state.brushes.length} brush image(s). 0 active (all disabled).`;
    return;
  }

  brushStatus.textContent =
    `Loaded ${state.brushes.length} brush image(s). ${enabledCount} active.`;
}

function createBrushActionButton(action, label, isActive, title) {
  const button = document.createElement("button");
  button.type = "button";
  button.className = "brush-action-button";
  if (isActive) {
    button.classList.add("is-active");
  }
  button.dataset.action = action;
  button.textContent = label;
  button.title = title;
  button.setAttribute("aria-label", title);
  button.setAttribute("aria-pressed", isActive ? "true" : "false");
  return button;
}

function renderBrushGallery() {
  brushGallery.innerHTML = "";

  if (!state.brushes.length) {
    dropZone.classList.remove("has-gallery");
    brushGallery.hidden = true;
    return;
  }

  dropZone.classList.add("has-gallery");
  brushGallery.hidden = false;

  const fragment = document.createDocumentFragment();
  const soloBrush = getSoloBrush();
  for (const brush of state.brushes) {
    const card = document.createElement("div");
    card.className = "brush-item";
    const isSolo = soloBrush && soloBrush.id === brush.id;
    if (!brush.enabled) {
      card.classList.add("is-disabled");
    }
    if (isSolo) {
      card.classList.add("is-solo");
    } else if (soloBrush) {
      card.classList.add("is-solo-muted");
    }
    card.dataset.brushId = String(brush.id);

    const preview = document.createElement("img");
    preview.className = "brush-thumb";
    preview.src = brush.url;
    preview.alt = brush.name;
    preview.draggable = false;

    const name = document.createElement("p");
    name.className = "brush-name";
    name.textContent = brush.name;

    const actionRow = document.createElement("div");
    actionRow.className = "brush-actions";

    const enabledButton = createBrushActionButton(
      "toggle-enabled",
      "👁",
      brush.enabled,
      brush.enabled
        ? "Disable brush image (right-click to solo)"
        : "Enable brush image (right-click to solo)"
    );
    if (isSolo) {
      enabledButton.classList.add("is-solo");
      enabledButton.title = "Solo brush active (right-click to unsolo)";
      enabledButton.setAttribute("aria-label", "Solo brush active");
    }
    const lowButton = createBrushActionButton(
      "weight-low",
      "-",
      brush.weightMode === "low",
      "Lower occurrence probability"
    );
    const highButton = createBrushActionButton(
      "weight-high",
      "+",
      brush.weightMode === "high",
      "Increase occurrence probability"
    );

    actionRow.appendChild(lowButton);
    actionRow.appendChild(enabledButton);
    actionRow.appendChild(highButton);
    card.appendChild(preview);
    card.appendChild(name);
    card.appendChild(actionRow);
    fragment.appendChild(card);
  }

  brushGallery.appendChild(fragment);
}

function onBrushGalleryClick(event) {
  const button = event.target.closest(".brush-action-button");
  if (!button) {
    return;
  }

  const item = button.closest(".brush-item");
  if (!item) {
    return;
  }

  const brushId = Number(item.dataset.brushId);
  const brush = findBrushById(brushId);
  if (!brush) {
    return;
  }

  const action = button.dataset.action;
  if (action === "toggle-enabled") {
    brush.enabled = !brush.enabled;
    if (!brush.enabled && state.soloBrushId === brush.id) {
      state.soloBrushId = null;
    }
  } else if (action === "weight-low") {
    brush.weightMode = brush.weightMode === "low" ? "normal" : "low";
  } else if (action === "weight-high") {
    brush.weightMode = brush.weightMode === "high" ? "normal" : "high";
  }

  updateBrushStatus();
  renderBrushGallery();
  scheduleSessionSave();
}

function onBrushGalleryContextMenu(event) {
  const eyeButton = event.target.closest(".brush-action-button[data-action=\"toggle-enabled\"]");
  if (!eyeButton) {
    return;
  }
  event.preventDefault();

  const item = eyeButton.closest(".brush-item");
  if (!item) {
    return;
  }

  const brushId = Number(item.dataset.brushId);
  const brush = findBrushById(brushId);
  if (!brush) {
    return;
  }

  if (state.soloBrushId === brush.id) {
    state.soloBrushId = null;
  } else {
    state.soloBrushId = brush.id;
    brush.enabled = true;
  }

  updateBrushStatus();
  renderBrushGallery();
  scheduleSessionSave();
}

function screenToWorld(clientX, clientY) {
  const rect = viewport.getBoundingClientRect();
  const screenX = clientX - rect.left;
  const screenY = clientY - rect.top;
  return {
    x: (screenX - state.camera.x) / state.camera.scale,
    y: (screenY - state.camera.y) / state.camera.scale
  };
}

function renderCamera() {
  world.style.transform =
    `translate(${state.camera.x}px, ${state.camera.y}px) scale(${state.camera.scale})`;
}

function isActiveBrushUrl(url) {
  for (const brush of state.brushes) {
    if (brush.url === url) {
      return true;
    }
  }
  return false;
}

function maybeReleaseObjectUrl(url) {
  if (!isBlobUrl(url)) {
    return;
  }

  const refCount = state.urlRefCounts.get(url) || 0;
  if (refCount === 0 && !isActiveBrushUrl(url)) {
    URL.revokeObjectURL(url);
  }
}

function incrementUrlRef(url) {
  const count = state.urlRefCounts.get(url) || 0;
  state.urlRefCounts.set(url, count + 1);
}

function decrementUrlRef(url) {
  if (!url) {
    return;
  }

  const nextCount = (state.urlRefCounts.get(url) || 0) - 1;
  if (nextCount <= 0) {
    state.urlRefCounts.delete(url);
    maybeReleaseObjectUrl(url);
  } else {
    state.urlRefCounts.set(url, nextCount);
  }
}

function detachStrokeFromWorld(stroke) {
  for (const element of stroke.elements) {
    decrementUrlRef(element.dataset.brushUrl);
    element.remove();
  }
}

function appendStrokeToWorld(stroke) {
  for (const element of stroke.elements) {
    world.appendChild(element);
    incrementUrlRef(element.dataset.brushUrl);
  }
}

function pushHistoryAction(action) {
  state.redoHistory = [];
  state.history.push(action);
  updateUndoState();
  updateBrushStatus();
  scheduleSessionSave();
}

function pushStroke(stroke) {
  if (!stroke.elements.length) {
    return;
  }

  state.strokes.push(stroke);
  state.strokeById.set(stroke.id, stroke);
  pushHistoryAction({ type: "draw", stroke });
}

function pushEraseAction(removals) {
  if (!Array.isArray(removals) || !removals.length) {
    return;
  }
  pushHistoryAction({ type: "erase", removals });
}

function undoEraseAction(action) {
  const removals = Array.isArray(action.removals) ? action.removals.slice() : [];
  removals.sort((left, right) => {
    const leftIndex = Number.isFinite(Number(left.worldIndex)) && Number(left.worldIndex) >= 0
      ? Number(left.worldIndex)
      : Number.MAX_SAFE_INTEGER;
    const rightIndex = Number.isFinite(Number(right.worldIndex)) && Number(right.worldIndex) >= 0
      ? Number(right.worldIndex)
      : Number.MAX_SAFE_INTEGER;
    return leftIndex - rightIndex;
  });

  for (const removal of removals) {
    if (!removal || !removal.element) {
      continue;
    }

    const stroke = removal.stroke || null;
    if (stroke && !state.strokeById.has(stroke.id)) {
      const preferredStrokeIndex =
        Number.isFinite(Number(removal.strokeIndex)) && Number(removal.strokeIndex) >= 0
        ? Number(removal.strokeIndex)
        : state.strokes.length;
      const insertStrokeIndex = Math.max(0, Math.min(preferredStrokeIndex, state.strokes.length));
      state.strokes.splice(insertStrokeIndex, 0, stroke);
      state.strokeById.set(stroke.id, stroke);
    }

    if (stroke && !stroke.elements.includes(removal.element)) {
      const preferredStampIndex =
        Number.isFinite(Number(removal.stampIndex)) && Number(removal.stampIndex) >= 0
        ? Number(removal.stampIndex)
        : stroke.elements.length;
      const insertStampIndex = Math.max(0, Math.min(preferredStampIndex, stroke.elements.length));
      stroke.elements.splice(insertStampIndex, 0, removal.element);
      removal.element.dataset.strokeId = String(stroke.id);
    }

    if (removal.element.parentElement !== world) {
      const preferredWorldIndex =
        Number.isFinite(Number(removal.worldIndex)) && Number(removal.worldIndex) >= 0
        ? Number(removal.worldIndex)
        : world.childElementCount;
      const insertWorldIndex = Math.max(0, Math.min(preferredWorldIndex, world.childElementCount));
      const beforeNode = world.children[insertWorldIndex] || null;
      world.insertBefore(removal.element, beforeNode);
      incrementUrlRef(removal.element.dataset.brushUrl);
    }
  }
}

function redoEraseAction(action) {
  const removals = Array.isArray(action.removals) ? action.removals : [];
  for (const removal of removals) {
    if (!removal || !removal.element) {
      continue;
    }
    removeStampElementFromState(removal.element);
  }
}

function undoDrawAction(action) {
  const stroke = action.stroke;
  if (!stroke) {
    return;
  }
  detachStrokeFromWorld(stroke);
  removeStrokeFromState(stroke);
}

function redoDrawAction(action) {
  const stroke = action.stroke;
  if (!stroke) {
    return true;
  }
  if (getVisibleStampCount() + stroke.elements.length > MAX_VISIBLE_STAMPS) {
    notifyStampLimitReached();
    return false;
  }
  appendStrokeToWorld(stroke);
  if (!state.strokeById.has(stroke.id)) {
    state.strokes.push(stroke);
    state.strokeById.set(stroke.id, stroke);
  }
  return true;
}

function undoLastStroke() {
  const action = state.history.pop();
  if (!action) {
    return;
  }

  if (action.type === "draw") {
    undoDrawAction(action);
  } else if (action.type === "erase") {
    undoEraseAction(action);
  } else {
    state.history.push(action);
    return;
  }

  state.redoHistory.push(action);
  updateUndoState();
  updateBrushStatus();
  scheduleSessionSave();
}

function redoLastStroke() {
  const action = state.redoHistory[state.redoHistory.length - 1];
  if (!action) {
    return;
  }

  let applied = false;
  if (action.type === "draw") {
    applied = redoDrawAction(action);
  } else if (action.type === "erase") {
    redoEraseAction(action);
    applied = true;
  }

  if (!applied) {
    return;
  }

  state.redoHistory.pop();
  state.history.push(action);
  updateUndoState();
  updateBrushStatus();
  scheduleSessionSave();
}

function clearAllStrokes() {
  while (state.strokes.length) {
    const stroke = state.strokes.pop();
    detachStrokeFromWorld(stroke);
  }
  state.strokeById.clear();
  state.history = [];
  state.redoHistory = [];
  clearCursorTrail();
  updateUndoState();
  updateBrushStatus();
  scheduleSessionSave();
}

function getBrushWeight(brush) {
  if (brush.weightMode === "low") {
    return LOW_WEIGHT_MULTIPLIER;
  }
  if (brush.weightMode === "high") {
    return HIGH_WEIGHT_MULTIPLIER;
  }
  return 1;
}

function pickRandomBrush() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    return soloBrush;
  }

  const candidates = state.brushes.filter((brush) => brush.enabled);
  if (!candidates.length) {
    return null;
  }

  let totalWeight = 0;
  for (const brush of candidates) {
    totalWeight += getBrushWeight(brush);
  }

  let randomWeight = Math.random() * totalWeight;
  for (const brush of candidates) {
    randomWeight -= getBrushWeight(brush);
    if (randomWeight <= 0) {
      return brush;
    }
  }

  return candidates[candidates.length - 1];
}

function placeBrush(x, y, stroke) {
  if (getVisibleStampCount() >= MAX_VISIBLE_STAMPS) {
    notifyStampLimitReached();
    return false;
  }

  const brush = pickRandomBrush();
  if (!brush) {
    return false;
  }

  let width = 0;
  let height = 0;
  if (consistentToggle.checked) {
    width = Math.max(4, Number(consistentSizeSlider.value));
    height = Math.max(4, width * (brush.height / brush.width));
  } else {
    const scale = Number(sizeSlider.value) / 100;
    width = Math.max(4, brush.width * scale);
    height = Math.max(4, brush.height * scale);
  }
  const stamp = document.createElement("img");

  stamp.className = "stamp";
  stamp.src = brush.url;
  stamp.alt = "";
  stamp.draggable = false;
  stamp.dataset.brushUrl = brush.url;
  stamp.dataset.brushId = String(brush.id);
  stamp.style.width = `${width}px`;
  stamp.style.height = `${height}px`;
  stamp.style.left = `${x - width / 2}px`;
  stamp.style.top = `${y - height / 2}px`;
  const rotation = parseNumericInputValue(rotationSlider, 0);
  stamp.dataset.rotation = String(rotation);
  stamp.style.opacity = String(clamp(Number(opacitySlider.value) / 100, 0, 1));
  stamp.style.imageRendering = renderModeToggle.checked ? "auto" : "pixelated";
  stamp.style.transform = `rotate(${rotation}deg)`;

  world.appendChild(stamp);
  incrementUrlRef(brush.url);
  stroke.elements.push(stamp);
  return true;
}

function placeAlongPath(drawing, x, y) {
  if (drawing.limitReached) {
    return;
  }

  const spacing = Number(spacingSlider.value);
  const dx = x - drawing.lastPlacedX;
  const dy = y - drawing.lastPlacedY;
  const distance = Math.hypot(dx, dy);

  if (distance < spacing) {
    return;
  }

  const stepX = dx / distance;
  const stepY = dy / distance;
  let remaining = distance;
  let cursorX = drawing.lastPlacedX;
  let cursorY = drawing.lastPlacedY;

  while (remaining >= spacing) {
    cursorX += stepX * spacing;
    cursorY += stepY * spacing;
    if (!placeBrush(cursorX, cursorY, drawing.stroke)) {
      drawing.limitReached = true;
      break;
    }
    remaining -= spacing;
  }

  drawing.lastPlacedX = cursorX;
  drawing.lastPlacedY = cursorY;
}

async function getImageDimensions(url) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => {
      resolve({
        width: Math.max(1, img.naturalWidth || img.width),
        height: Math.max(1, img.naturalHeight || img.height)
      });
    };
    img.onerror = reject;
    img.src = url;
  });
}

async function readFileAsDataUrl(file) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(String(reader.result || ""));
    reader.onerror = () => reject(reader.error || new Error("Could not read file data."));
    reader.readAsDataURL(file);
  });
}

function isAllowedImage(file) {
  if (!file || !file.name) {
    return false;
  }
  return ALLOWED_EXTENSIONS.test(file.name);
}

async function loadBrushFiles(files) {
  const validFiles = files.filter(isAllowedImage);
  if (!validFiles.length) {
    updateBrushStatus("No supported image files found.");
    return;
  }

  const previousBrushUrls = state.brushes.map((brush) => brush.url);

  const loaded = [];
  for (const file of validFiles) {
    try {
      const dataUrl = await readFileAsDataUrl(file);
      if (!dataUrl) {
        continue;
      }
      const dimensions = await getImageDimensions(dataUrl);
      loaded.push({
        id: state.nextBrushId,
        url: dataUrl,
        name: file.name,
        width: dimensions.width,
        height: dimensions.height,
        enabled: true,
        weightMode: "normal"
      });
      state.nextBrushId += 1;
    } catch (error) {
      // Skip unreadable files and continue loading the rest.
    }
  }

  state.brushes = loaded;
  state.soloBrushId = null;
  for (const oldUrl of previousBrushUrls) {
    maybeReleaseObjectUrl(oldUrl);
  }

  if (state.brushes.length) {
    updateBrushStatus();
    renderBrushGallery();
    scheduleSessionSave();
  } else {
    updateBrushStatus("Could not load image data from selection.");
    renderBrushGallery();
    scheduleSessionSave();
  }
}

async function fileFromEntry(entry) {
  return new Promise((resolve) => {
    entry.file(
      (file) => resolve(file),
      () => resolve(null)
    );
  });
}

async function entriesFromDirectoryEntry(directoryEntry) {
  const reader = directoryEntry.createReader();
  const entries = [];

  while (true) {
    const batch = await new Promise((resolve) => {
      reader.readEntries(resolve, () => resolve([]));
    });

    if (!batch.length) {
      break;
    }
    entries.push(...batch);
  }

  return entries;
}

async function collectFromWebkitEntry(entry, output) {
  if (!entry) {
    return;
  }

  if (entry.isFile) {
    const file = await fileFromEntry(entry);
    if (file) {
      output.push(file);
    }
    return;
  }

  if (entry.isDirectory) {
    const entries = await entriesFromDirectoryEntry(entry);
    for (const child of entries) {
      await collectFromWebkitEntry(child, output);
    }
  }
}

async function collectFromHandle(handle, output) {
  if (!handle) {
    return;
  }

  if (handle.kind === "file") {
    const file = await handle.getFile();
    output.push(file);
    return;
  }

  if (handle.kind === "directory") {
    for await (const childHandle of handle.values()) {
      await collectFromHandle(childHandle, output);
    }
  }
}

async function collectFilesFromDataTransfer(dataTransfer) {
  const files = [];
  const items = Array.from(dataTransfer.items || []);

  if (items.length && typeof items[0].getAsFileSystemHandle === "function") {
    for (const item of items) {
      try {
        const handle = await item.getAsFileSystemHandle();
        await collectFromHandle(handle, files);
      } catch (error) {
        // Continue with best-effort extraction from remaining items.
      }
    }
    if (files.length) {
      return files;
    }
  }

  if (items.length && typeof items[0].webkitGetAsEntry === "function") {
    for (const item of items) {
      const entry = item.webkitGetAsEntry();
      await collectFromWebkitEntry(entry, files);
    }
    if (files.length) {
      return files;
    }
  }

  return Array.from(dataTransfer.files || []);
}

function startErasing(event) {
  const point = screenToWorld(event.clientX, event.clientY);
  const radiusWorld = getCurrentEraserDiameterWorld() / 2;
  const removalContext = {
    records: [],
    worldOrder: new Map(Array.from(world.children).map((element, index) => [element, index]))
  };
  const changed = eraseAtPoint(point.x, point.y, radiusWorld, removalContext);

  state.erasing = {
    pointerId: event.pointerId,
    lastX: point.x,
    lastY: point.y,
    changed,
    removalContext
  };
  viewport.setPointerCapture(event.pointerId);
}

function stopErasing(pointerId) {
  if (!state.erasing || state.erasing.pointerId !== pointerId) {
    return;
  }

  if (viewport.hasPointerCapture(pointerId)) {
    viewport.releasePointerCapture(pointerId);
  }

  const erasing = state.erasing;
  const changed = erasing.changed;
  const removals = erasing.removalContext.records;
  state.erasing = null;
  if (changed && removals.length) {
    pushEraseAction(removals);
  }
}

function startDrawing(event) {
  if (!state.brushes.length) {
    updateBrushStatus("Load brush data before drawing.");
    return;
  }

  if (!hasEnabledBrushes()) {
    updateBrushStatus("Enable at least one brush image before drawing.");
    return;
  }

  const point = screenToWorld(event.clientX, event.clientY);
  const stroke = { id: state.nextStrokeId, elements: [] };
  state.nextStrokeId += 1;

  if (!placeBrush(point.x, point.y, stroke)) {
    return;
  }

  state.drawing = {
    pointerId: event.pointerId,
    stroke,
    lastPlacedX: point.x,
    lastPlacedY: point.y,
    limitReached: false
  };
  viewport.setPointerCapture(event.pointerId);
}

function stopDrawing(pointerId) {
  if (!state.drawing || state.drawing.pointerId !== pointerId) {
    return;
  }

  pushStroke(state.drawing.stroke);
  if (viewport.hasPointerCapture(pointerId)) {
    viewport.releasePointerCapture(pointerId);
  }
  state.drawing = null;
}

function startPanning(event) {
  resetCursorTrailAnchor();
  state.panning = {
    pointerId: event.pointerId,
    lastClientX: event.clientX,
    lastClientY: event.clientY
  };
  viewport.classList.add("is-panning");
  viewport.setPointerCapture(event.pointerId);
}

function stopPanning(pointerId) {
  if (!state.panning || state.panning.pointerId !== pointerId) {
    return;
  }

  viewport.classList.remove("is-panning");
  if (viewport.hasPointerCapture(pointerId)) {
    viewport.releasePointerCapture(pointerId);
  }
  state.panning = null;
  updateEraseCursorVisibility();
  scheduleSessionSave();
}

function onPointerDown(event) {
  state.pointerInViewport = true;
  state.lastPointerClientX = event.clientX;
  state.lastPointerClientY = event.clientY;
  updateEraseCursorPosition(event.clientX, event.clientY);
  updateEraseCursorVisibility();

  if (event.button === 1 || event.button === 2) {
    event.preventDefault();
    startPanning(event);
    updateEraseCursorVisibility();
    return;
  }

  if (event.button !== 0) {
    return;
  }

  event.preventDefault();
  if (state.eraseMode) {
    startErasing(event);
    return;
  }

  startDrawing(event);
}

function onPointerMove(event) {
  state.pointerInViewport = true;
  state.lastPointerClientX = event.clientX;
  state.lastPointerClientY = event.clientY;
  updateEraseCursorPosition(event.clientX, event.clientY);
  updateEraseCursorVisibility();

  if (state.panning && state.panning.pointerId === event.pointerId) {
    event.preventDefault();
    const dx = event.clientX - state.panning.lastClientX;
    const dy = event.clientY - state.panning.lastClientY;
    state.camera.x += dx;
    state.camera.y += dy;
    state.panning.lastClientX = event.clientX;
    state.panning.lastClientY = event.clientY;
    renderCamera();
  }

  if (state.drawing && state.drawing.pointerId === event.pointerId) {
    event.preventDefault();
    const point = screenToWorld(event.clientX, event.clientY);
    placeAlongPath(state.drawing, point.x, point.y);
  }

  if (state.erasing && state.erasing.pointerId === event.pointerId) {
    event.preventDefault();
    const point = screenToWorld(event.clientX, event.clientY);
    eraseAlongPath(state.erasing, point.x, point.y);
  }

  updateCursorTrailAtClientPoint(event.clientX, event.clientY);
}

function onPointerUp(event) {
  stopPanning(event.pointerId);
  stopErasing(event.pointerId);
  stopDrawing(event.pointerId);
  updateEraseCursorVisibility();
}

function onWheel(event) {
  event.preventDefault();
  resetCursorTrailAnchor();

  const rect = viewport.getBoundingClientRect();
  const cursorX = event.clientX - rect.left;
  const cursorY = event.clientY - rect.top;
  const worldX = (cursorX - state.camera.x) / state.camera.scale;
  const worldY = (cursorY - state.camera.y) / state.camera.scale;

  const zoomFactor = Math.exp(-event.deltaY * 0.0015);
  const nextScale = clamp(state.camera.scale * zoomFactor, MIN_CAMERA_SCALE, MAX_CAMERA_SCALE);

  state.camera.x = cursorX - worldX * nextScale;
  state.camera.y = cursorY - worldY * nextScale;
  state.camera.scale = nextScale;
  renderCamera();
  updateEraseCursorGeometry();
  scheduleSessionSave();
}

function onDropZoneKeyDown(event) {
  if (event.key === "Enter" || event.key === " ") {
    event.preventDefault();
    brushInput.click();
  }
}

function openClearConfirmModal() {
  if (getVisibleStampCount() === 0) {
    return;
  }
  clearConfirmModal.classList.add("is-open");
  clearConfirmModal.setAttribute("aria-hidden", "false");
  confirmNoButton.focus();
}

function closeClearConfirmModal() {
  clearConfirmModal.classList.remove("is-open");
  clearConfirmModal.setAttribute("aria-hidden", "true");
  clearButton.focus();
}

function setEraseMode(nextValue) {
  state.eraseMode = Boolean(nextValue);
  if (state.eraseMode) {
    clearCursorTrail();
  }
  if (!state.eraseMode && state.erasing) {
    stopErasing(state.erasing.pointerId);
  }
  if (state.pointerInViewport) {
    updateEraseCursorPosition(state.lastPointerClientX, state.lastPointerClientY);
  }
  updateEraseModeUI();
}

dropZonePrompt.addEventListener("click", () => brushInput.click());
dropZonePrompt.addEventListener("keydown", onDropZoneKeyDown);
brushGallery.addEventListener("click", onBrushGalleryClick);
brushGallery.addEventListener("contextmenu", onBrushGalleryContextMenu);
dropZone.addEventListener("dragover", (event) => {
  event.preventDefault();
  dropZone.classList.add("is-over");
});
dropZone.addEventListener("dragleave", () => {
  dropZone.classList.remove("is-over");
});
dropZone.addEventListener("drop", async (event) => {
  event.preventDefault();
  dropZone.classList.remove("is-over");
  const files = await collectFilesFromDataTransfer(event.dataTransfer);
  await loadBrushFiles(files);
});

brushInput.addEventListener("change", async () => {
  const files = Array.from(brushInput.files || []);
  await loadBrushFiles(files);
  brushInput.value = "";
});

sizeSlider.addEventListener("input", () => {
  updateSliderText();
  updateEraseCursorGeometry();
  scheduleSessionSave();
});
consistentToggle.addEventListener("change", () => {
  updateConsistentModeUI();
  updateEraseCursorGeometry();
  scheduleSessionSave();
});
consistentSizeSlider.addEventListener("input", () => {
  updateSliderText();
  updateEraseCursorGeometry();
  scheduleSessionSave();
});
spacingSlider.addEventListener("input", () => {
  updateSliderText();
  scheduleSessionSave();
});
rotationSlider.addEventListener("input", () => {
  updateSliderText();
  updateRotationIndicator();
  scheduleSessionSave();
});
rotationIndicator.addEventListener("dblclick", (event) => {
  event.preventDefault();
  setInputNumericValue(rotationSlider, 0);
  updateSliderText();
  updateRotationIndicator();
  scheduleSessionSave();
});
opacitySlider.addEventListener("input", () => {
  updateSliderText();
  scheduleSessionSave();
});
renderModeToggle.addEventListener("change", () => {
  updateRenderModeUI();
  scheduleSessionSave();
});
cursorTrailToggle.addEventListener("change", () => {
  updateCursorTrailUI();
  scheduleSessionSave();
});
cursorTrailCountSlider.addEventListener("input", () => {
  updateSliderText();
  enforceCursorTrailLimit();
  scheduleSessionSave();
});
sidebarToggleButton.addEventListener("click", () => {
  state.sidebarCollapsed = !state.sidebarCollapsed;
  updateSidebarVisibilityUI();
  scheduleSessionSave();
});
eraseModeButton.addEventListener("click", () => {
  setEraseMode(!state.eraseMode);
});
undoButton.addEventListener("click", undoLastStroke);
redoButton.addEventListener("click", redoLastStroke);
clearButton.addEventListener("click", openClearConfirmModal);
confirmYesButton.addEventListener("click", () => {
  clearAllStrokes();
  closeClearConfirmModal();
});
confirmNoButton.addEventListener("click", closeClearConfirmModal);
clearConfirmModal.addEventListener("click", (event) => {
  if (event.target === clearConfirmModal) {
    closeClearConfirmModal();
  }
});
document.addEventListener("keydown", (event) => {
  const key = String(event.key || "").toLowerCase();
  const hasUndoModifier = event.ctrlKey || event.metaKey;
  if (hasUndoModifier && !event.altKey && key === "z") {
    event.preventDefault();
    if (event.shiftKey) {
      redoLastStroke();
    } else {
      undoLastStroke();
    }
    return;
  }

  if (event.key === "Escape" && clearConfirmModal.classList.contains("is-open")) {
    closeClearConfirmModal();
  }
});

viewport.addEventListener("pointerdown", onPointerDown);
viewport.addEventListener("pointermove", onPointerMove);
viewport.addEventListener("pointerup", onPointerUp);
viewport.addEventListener("pointercancel", onPointerUp);
viewport.addEventListener("pointerenter", (event) => {
  state.pointerInViewport = true;
  state.lastPointerClientX = event.clientX;
  state.lastPointerClientY = event.clientY;
  updateEraseCursorPosition(event.clientX, event.clientY);
  updateEraseCursorVisibility();
});
viewport.addEventListener("pointerleave", () => {
  state.pointerInViewport = false;
  resetCursorTrailAnchor();
  updateEraseCursorVisibility();
});
viewport.addEventListener("wheel", onWheel, { passive: false });
viewport.addEventListener("contextmenu", (event) => event.preventDefault());
viewport.addEventListener("auxclick", (event) => {
  if (event.button === 1) {
    event.preventDefault();
  }
});
window.addEventListener("pagehide", flushSessionSaveNow);
window.addEventListener("beforeunload", flushSessionSaveNow);
document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "hidden") {
    flushSessionSaveNow();
  }
});

async function initializeApp() {
  const restored = await restoreSessionState();
  if (restored) {
    return;
  }
  updateSliderText();
  updateConsistentModeUI();
  updateRenderModeUI();
  updateCursorTrailUI();
  updateRotationIndicator();
  updateSidebarVisibilityUI();
  updateEraseModeUI();
  updateUndoState();
  updateBrushStatus();
  renderBrushGallery();
  renderCamera();
}

void initializeApp();
