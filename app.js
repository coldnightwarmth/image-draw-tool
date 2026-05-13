const MAX_VISIBLE_STAMPS = 25000;
const ALLOWED_EXTENSIONS = /\.(png|jpe?g|webp|gif)$/i;
const STOCK_BRUSH_FOLDERS = Array.isArray(window.STOCK_BRUSH_FOLDERS)
  ? window.STOCK_BRUSH_FOLDERS
  : [];
const STOCK_BRUSH_FOLDER_ORDER = [
  "radial",
  "flower",
  "garden",
  "stroke",
  "squares",
  "futari glitch",
  "esp ra de glitch",
  "laser data",
  "particles",
  "3d",
  "pixel art+games",
  "anime",
  "misc",
  "esp ra de",
  "esp ra de characters",
  "framing"
];
const DRAW_MODES = ["pencil", "spray", "line", "box", "circle"];
const SHAPE_DRAW_MODES = new Set(["line", "box", "circle"]);
const SIDEBAR_TABS = ["draw", "brushes", "edit", "export", "community", "settings"];
const EDIT_LAYER_LIVE_MOVE_LIMIT = 1000;
const MAX_LAYER_SEQUENCE_EFFECTS = 3;
const LAYER_SEQUENCE_EFFECT_OPTIONS = [
  { value: "show-hide", label: "Show/Hide" },
  { value: "move", label: "Move" },
  { value: "rotate", label: "Rotate" },
  { value: "scale", label: "Scale" },
  { value: "color-cycle", label: "Color Cycle" },
  { value: "image-cycle", label: "Image Cycle" }
];
const LAYER_SEQUENCE_TIMING_OPTIONS = [
  { value: "pulse", label: "Pulse" },
  { value: "wave", label: "Bounce" },
  { value: "step", label: "Step" },
  { value: "random", label: "Random" },
  { value: "all", label: "All" }
];
const LAYER_SEQUENCE_MOVE_MODE_OPTIONS = [
  { value: "left", label: "left" },
  { value: "right", label: "right" },
  { value: "up", label: "up" },
  { value: "down", label: "down" },
  { value: "circle", label: "circle" },
  { value: "swing", label: "swing" },
  { value: "random", label: "random" }
];
const LAYER_SEQUENCE_DEFAULT_SETTINGS = {
  showHideFade: false,
  showHideFadeLength: 300,
  moveInstant: false,
  moveMode: "left",
  moveStrength: 80,
  moveSpeed: 45,
  colorCycleColor: "#ff00ff",
  colorCycleAmount: 70,
  colorCycleInstant: false,
  colorCycleSpeed: 45,
  rotateSpeed: 45,
  rotateContinuous: false,
  rotateReverse: false,
  scaleSpeed: 45,
  scaleAmount: 50,
  imageCycleRandom: false,
  imageCycleSpeed: 50,
  pulseSpeed: 35,
  pulseRate: 35,
  waveSpeed: 45,
  waveReverse: false,
  stepLength: 350,
  stepAmount: 1,
  randomSpeed: 45
};
const SESSION_STORAGE_KEY = "random-brush-drawer-session-v1";
const SESSION_STORAGE_POINTER_KEY = `${SESSION_STORAGE_KEY}-pointer`;
const SESSION_STORAGE_TAB_ID_KEY = `${SESSION_STORAGE_KEY}-tab-id`;
const SESSION_IDB_PREFIX = "idb:";
const SESSION_IDB_NAME = "image-brush-session-cache";
const SESSION_IDB_STORE_NAME = "snapshots";
const SAVED_COMPOSITIONS_INDEX_KEY = "saved-compositions:index";
const SAVED_COMPOSITION_KEY_PREFIX = "saved-composition:";
const FAVORITE_BRUSH_SOURCES_KEY = "favorite-brush-sources:v1";
const CUSTOM_BRUSH_PRESET_SOURCES_KEY = "custom-brush-preset-sources:v1";
const SAVE_DEBOUNCE_MS = 140;

const viewport = document.getElementById("viewport");
const world = document.getElementById("world");
const controlsPanel = document.getElementById("controls");
const controlsMain = document.getElementById("controlsMain");
const settingsPanel = document.getElementById("settingsPanel");
const sidebarOptionsButton = document.getElementById("sidebarOptionsButton");
const sidebarToggleButton = document.getElementById("sidebarToggleButton");
const sidebarPanels = Array.from(document.querySelectorAll("[data-sidebar-panel]"));
const mainModeBar = document.getElementById("mainModeBar");
const mainModeTabButtons = Array.from(document.querySelectorAll(".main-mode-tab-button"));
const drawingBrushDataSlot = document.getElementById("drawingBrushDataSlot");
const brushDataPanel = document.getElementById("brushDataPanel");
const brushDataControlGroup = document.getElementById("brushDataControlGroup");
const editLayerList = document.getElementById("editLayerList");
const editLayerDeleteDropzone = document.getElementById("editLayerDeleteDropzone");
const saveCompositionButton = document.getElementById("saveCompositionButton");
const savedCompositionsStatus = document.getElementById("savedCompositionsStatus");
const savedCompositionsGallery = document.getElementById("savedCompositionsGallery");
const brushDataToggleButton = document.getElementById("brushDataToggleButton");
const dropZone = document.getElementById("dropZone");
const dropZoneHeader = document.getElementById("dropZoneHeader");
const dropZonePrompt = document.getElementById("dropZonePrompt");
const unloadBrushDataButton = document.getElementById("unloadBrushDataButton");
const brushGallery = document.getElementById("brushGallery");
const stockBrushButtons = document.getElementById("stockBrushButtons");
const brushSortControls = document.getElementById("brushSortControls");
const brushSortSelect = document.getElementById("brushSortSelect");
const loadAllStockBrushesButton = document.getElementById("loadAllStockBrushesButton");
const loadFavoriteBrushesButton = document.getElementById("loadFavoriteBrushesButton");
const loadFavoriteBrushesFullButton = document.getElementById("loadFavoriteBrushesFullButton");
const drawingBrushPresetButtons = document.getElementById("drawingBrushPresetButtons");
const brushesBrushPresetButtons = document.getElementById("brushesBrushPresetButtons");
const brushInput = document.getElementById("brushInput");
const brushStatus = document.getElementById("brushStatus");
const sizeScaleGroup = document.getElementById("sizeScaleGroup");
const sizeControlLabel = document.getElementById("sizeControlLabel");
const sizePercentGroup = document.getElementById("sizePercentGroup");
const sizeSlider = document.getElementById("sizeSlider");
const sizeValue = document.getElementById("sizeValue");
const consistentToggle = document.getElementById("consistentToggle");
const consistentSizeGroup = document.getElementById("consistentSizeGroup");
const consistentSizeSlider = document.getElementById("consistentSizeSlider");
const consistentSizeValue = document.getElementById("consistentSizeValue");
const sizePercentValueText = document.getElementById("sizePercentValueText");
const consistentSizeValueText = document.getElementById("consistentSizeValueText");
const spacingSlider = document.getElementById("spacingSlider");
const spacingValue = document.getElementById("spacingValue");
const rotationSlider = document.getElementById("rotationSlider");
const rotationValue = document.getElementById("rotationValue");
const rotationIndicator = document.getElementById("rotationIndicator");
const rotationNeedle = document.getElementById("rotationNeedle");
const tintPickerButton = document.getElementById("tintPickerButton");
const tintSwatch = document.getElementById("tintSwatch");
const tintPopover = document.getElementById("tintPopover");
const tintGroup = document.getElementById("tintGroup");
const tintColorField = document.getElementById("tintColorField");
const tintColorInput = document.getElementById("tintColorInput");
const tintAmountSlider = document.getElementById("tintAmountSlider");
const tintAmountValue = document.getElementById("tintAmountValue");
const drawCanvasBgRow = document.getElementById("drawCanvasBgRow");
const drawCanvasBgColorLabel = document.getElementById("drawCanvasBgColorLabel");
const drawCanvasBgColorInput = document.getElementById("drawCanvasBgColorInput");
const canvasBgColorLabel = document.getElementById("canvasBgColorLabel");
const canvasBgColorInput = document.getElementById("canvasBgColorInput");
const exportCanvasBgRow = document.getElementById("exportCanvasBgRow");
const exportCanvasBgColorLabel = document.getElementById("exportCanvasBgColorLabel");
const exportCanvasBgColorInput = document.getElementById("exportCanvasBgColorInput");
const exportBgImageButton = document.getElementById("exportBgImageButton");
const clearExportBgImageButton = document.getElementById("clearExportBgImageButton");
const exportBgImagePreview = document.getElementById("exportBgImagePreview");
const exportBgImageInput = document.getElementById("exportBgImageInput");
const exportBgImageControls = document.getElementById("exportBgImageControls");
const exportBgImageOpacitySlider = document.getElementById("exportBgImageOpacitySlider");
const exportBgImageOpacityValue = document.getElementById("exportBgImageOpacityValue");
const exportBgImageModeLabel = document.getElementById("exportBgImageModeLabel");
const exportBgImageTileToggle = document.getElementById("exportBgImageTileToggle");
const exportBgImageTileSizeGroup = document.getElementById("exportBgImageTileSizeGroup");
const exportBgImageTileSizeSlider = document.getElementById("exportBgImageTileSizeSlider");
const exportBgImageTileSizeValue = document.getElementById("exportBgImageTileSizeValue");
const exportBackgroundToggle = document.getElementById("exportBackgroundToggle");
const exportSeeBeyondToggle = document.getElementById("exportSeeBeyondToggle");
const gifCountToggle = document.getElementById("gifCountToggle");
const gifCountIndicator = document.getElementById("gifCountIndicator");
const gifPauseToggle = document.getElementById("gifPauseToggle");
const drawBkgColorToggle = document.getElementById("drawBkgColorToggle");
const brushPreviewToggle = document.getElementById("brushPreviewToggle");
const filterDefs = document.getElementById("filterDefs");
const opacitySlider = document.getElementById("opacitySlider");
const opacityValue = document.getElementById("opacityValue");
const renderModeToggle = document.getElementById("renderModeToggle");
const renderModeLabel = document.getElementById("renderModeLabel");
const cursorTrailToggle = document.getElementById("cursorTrailToggle");
const cursorTrailCountGroup = document.getElementById("cursorTrailCountGroup");
const cursorTrailCountSlider = document.getElementById("cursorTrailCountSlider");
const cursorTrailCountValue = document.getElementById("cursorTrailCountValue");
const eraseCursor = document.getElementById("eraseCursor");
const shapePreview = document.getElementById("shapePreview");
const brushCursorPreview = document.getElementById("brushCursorPreview");
const shortcutPreview = document.getElementById("shortcutPreview");
const drawModeButtons = document.getElementById("drawModeButtons");
const spraySpreadGroup = document.getElementById("spraySpreadGroup");
const spraySpreadSlider = document.getElementById("spraySpreadSlider");
const spraySpreadValue = document.getElementById("spraySpreadValue");
const eraseModeButton = document.getElementById("eraseModeButton");
const undoButton = document.getElementById("undoButton");
const redoButton = document.getElementById("redoButton");
const clearButton = document.getElementById("clearButton");
const exportActions = document.getElementById("exportActions");
const exportModeButton = document.getElementById("exportModeButton");
const exportButton = document.getElementById("exportButton");
const exportCancelButton = document.getElementById("exportCancelButton");
const gifPauseButton = document.getElementById("gifPauseButton");
const clearConfirmModal = document.getElementById("clearConfirmModal");
const confirmYesButton = document.getElementById("confirmYesButton");
const confirmNoButton = document.getElementById("confirmNoButton");
const savedDeleteConfirmModal = document.getElementById("savedDeleteConfirmModal");
const savedDeleteConfirmYesButton = document.getElementById("savedDeleteConfirmYesButton");
const savedDeleteConfirmNoButton = document.getElementById("savedDeleteConfirmNoButton");
const brushCropModal = document.getElementById("brushCropModal");
const brushCropDialog = document.getElementById("brushCropDialog");
const brushCropStage = document.getElementById("brushCropStage");
const brushCropImage = document.getElementById("brushCropImage");
const brushCropSelection = document.getElementById("brushCropSelection");
const brushCropShadeTop = document.getElementById("brushCropShadeTop");
const brushCropShadeRight = document.getElementById("brushCropShadeRight");
const brushCropShadeBottom = document.getElementById("brushCropShadeBottom");
const brushCropShadeLeft = document.getElementById("brushCropShadeLeft");
const brushCropConfirmButton = document.getElementById("brushCropConfirmButton");
const brushCropCancelButton = document.getElementById("brushCropCancelButton");
const brushCropWidthInput = document.getElementById("brushCropWidthInput");
const brushCropHeightInput = document.getElementById("brushCropHeightInput");
const brushCropResolutionResetButton = document.getElementById("brushCropResolutionResetButton");
const brushCropFrameControls = document.getElementById("brushCropFrameControls");
const brushCropFrameTrack = document.getElementById("brushCropFrameTrack");
const brushCropFrameSegments = document.getElementById("brushCropFrameSegments");
const brushCropFrameSelection = document.getElementById("brushCropFrameSelection");
const brushCropFrameStartHandle = document.getElementById("brushCropFrameStartHandle");
const brushCropFrameEndHandle = document.getElementById("brushCropFrameEndHandle");
const brushCropFrameReadout = document.getElementById("brushCropFrameReadout");
const brushCropProbabilityControls = document.getElementById("brushCropProbabilityControls");
const brushCropProbabilityButtons = brushCropProbabilityControls
  ? Array.from(brushCropProbabilityControls.querySelectorAll(".brush-crop-probability-button"))
  : [];
const exportOverlay = document.getElementById("exportOverlay");
const exportShadeTop = document.getElementById("exportShadeTop");
const exportShadeRight = document.getElementById("exportShadeRight");
const exportShadeBottom = document.getElementById("exportShadeBottom");
const exportShadeLeft = document.getElementById("exportShadeLeft");
const exportSelection = document.getElementById("exportSelection");
const exportBgImageLayer = document.getElementById("exportBgImageLayer");
const exportMeta = document.getElementById("exportMeta");
const exportWidthInput = document.getElementById("exportWidthInput");
const exportHeightInput = document.getElementById("exportHeightInput");
const exportSidebarWidthInput = document.getElementById("exportSidebarWidthInput");
const exportSidebarHeightInput = document.getElementById("exportSidebarHeightInput");
const exportScaleButtonsGroup = document.getElementById("exportScaleButtons");
const exportSidebarScaleButtonsGroup = document.getElementById("exportSidebarScaleButtons");
const exportAnimationDurationLabel = document.getElementById("exportAnimationDurationLabel");
const exportAnimationAutoToggle = document.getElementById("exportAnimationAutoToggle");
const exportAnimationManualControls = document.getElementById("exportAnimationManualControls");
const exportAnimationSecondsButtonsGroup = document.getElementById("exportAnimationSecondsButtons");
const exportAnimationSecondsButtons = exportAnimationSecondsButtonsGroup
  ? Array.from(exportAnimationSecondsButtonsGroup.querySelectorAll(".export-animation-seconds-button"))
  : [];
const exportFrameCountInput = document.getElementById("exportFrameCountInput");
const exportVideoDurationLabel = document.getElementById("exportVideoDurationLabel");
const exportVideoAutoToggle = document.getElementById("exportVideoAutoToggle");
const exportVideoLengthRow = document.getElementById("exportVideoLengthRow");
const exportVideoLengthInput = document.getElementById("exportVideoLengthInput");
const exportVideoButton = document.getElementById("exportVideoButton");
const exportVideoCancelButton = document.getElementById("exportVideoCancelButton");
const exportScaleButtons = Array.from(
  exportOverlay.querySelectorAll(".export-scale-button")
);
const exportSidebarScaleButtons = exportSidebarScaleButtonsGroup
  ? Array.from(exportSidebarScaleButtonsGroup.querySelectorAll(".export-scale-button"))
  : [];
const sliderToggleLabels = Array.from(
  document.querySelectorAll(".slider-toggle-label[data-slider-toggle-target]")
);

const BRUSH_WEIGHT_MULTIPLIERS = {
  standard: 8,
  common: 3,
  normal: 1,
  uncommon: 0.35,
  rare: 0.08,
  low: 0.35,
  high: 3
};
const ERASER_PERCENT_SIZE_MULTIPLIER = 2;
const ERASER_GLOBAL_SIZE_MULTIPLIER = 2.5;
const MIN_CAMERA_SCALE = 0.005;
const MAX_CAMERA_SCALE = 6;
const CURSOR_TRAIL_FADE_MS = 4000;
const EXPORT_SELECTION_PADDING = 18;
const EXPORT_MIN_SIZE = 24;
const EXPORT_GIF_DURATION_MS = 2000;
const EXPORT_GIF_FRAME_DELAY_MS = 50;
const EXPORT_MAX_FRAME_COUNT = 512;
const EXPORT_MANUAL_SECONDS_PRESETS = [0.5, 1, 2, 3, 4, 5];
const EXPORT_VIDEO_MAX_DIMENSION = 1600;
const EXPORT_VIDEO_MAX_SECONDS = 300;
const EXPORT_VIDEO_FPS = 30;
const EXPORT_PROGRESS_COLLECT_END = 5;
const EXPORT_PROGRESS_DECODE_END = 18;
const EXPORT_PROGRESS_DRAW_END = 55;
const EXPORT_PROGRESS_PNG_ENCODE_HOLD = 88;
const EXPORT_PROGRESS_ENCODE_END = 99;
const EXPORT_BG_TILE_MIN_SIZE = 8;
const EXPORT_BG_TILE_MID_SIZE = 1000;
const EXPORT_BG_TILE_MAX_SIZE = 5000;
const EXPORT_BG_TILE_SLIDER_MAX = 1000;
const EXPORT_BG_TILE_SLIDER_MID = 750;
const GIF_JS_LIBRARY_URL = "gif.js";
const GIF_JS_WORKER_URL = "gif.worker.js";
const GIFUCT_MODULE_URL = "./gifuct-js.bundle.mjs";
const EXPORT_MIN_DIMENSION = 1;
const EXPORT_MAX_DIMENSION = 10000;
const EXPORT_SCALE_PRESETS = [5, 10, 25, 50, 100, 200];
const BRUSH_CROP_MIN_SIZE = 4;
const GIF_TRANSPARENT_MATTE = "#00ff01";
const GIF_TRANSPARENT_MATTE_HEX = 0x00ff01;
const STAMP_INDEX_CELL_SIZE = 256;
const STAMP_VIEWPORT_CULL_MARGIN_PX = 640;
const TRANSPARENT_STAMP_SRC =
  "data:image/gif;base64,R0lGODlhAQABAIAAAAAAAP///ywAAAAAAQABAAACAUwAOw==";
const ERASER_SAMPLE_GRID_SIZE = 5;
const ERASER_PATH_STEP_FACTOR = 0.6;
const ERASER_PATH_MIN_STEP = 6;
const ERASER_MAX_SAMPLES_PER_FRAME = 24;
const SPRAY_MIN_STAMPS = 3;
const SPRAY_MAX_STAMPS = 34;
const DEFAULT_SPRAY_SPREAD = 256;
const SHAPE_DRAG_THRESHOLD_PX = 5;
const PLACEMENT_CANCEL_CHECK_INTERVAL = 40;
const EXPORT_CANCEL_CHECK_INTERVAL = 40;
const BRUSH_FRAME_COUNT_DECODE_CONCURRENCY = 2;
const SEQUENCE_INTERRUPT_TWEEN_MS = 160;
const SEQUENCE_TRIGGER_PRIME_MS = 16;
const SEQUENCE_DATASET_KEYS = [
  "sequenceActive",
  "sequenceBaseOpacity",
  "sequenceBaseSrc",
  "sequenceImageCycleKey",
  "sequenceImageCycleSrc",
  "sequenceTriggerKey",
  "sequenceHidden",
  "sequenceVisibilityStart",
  "sequenceVisibilityFrom",
  "sequenceVisibilityTo",
  "sequenceVisibilityDuration",
  "sequenceMoveStart",
  "sequenceMoveFromX",
  "sequenceMoveFromY",
  "sequenceMoveToX",
  "sequenceMoveToY",
  "sequenceMoveDuration",
  "sequenceMoveExpanded",
  "sequenceMoveCircleStep",
  "sequenceRotateStart",
  "sequenceRotateFrom",
  "sequenceRotateTo",
  "sequenceRotateDuration",
  "sequenceRotateContinuousStart",
  "sequenceRotateContinuousActive",
  "sequenceRotateRestAngle",
  "sequenceScaleStart",
  "sequenceScaleFrom",
  "sequenceScaleTo",
  "sequenceScaleDuration",
  "sequenceScaleTarget",
  "sequenceScaleExpanded",
  "sequenceColorStart",
  "sequenceColorFrom",
  "sequenceColorTo",
  "sequenceColorDuration",
  "sequenceColorTarget",
  "sequenceColorShifted"
];
const SEQUENCE_BASE_DATASET_KEYS = [
  "sequenceActive",
  "sequenceBaseOpacity",
  "sequenceBaseSrc"
];
const SEQUENCE_SLOT_STATE_KEYS = SEQUENCE_DATASET_KEYS.filter(
  (key) => !SEQUENCE_BASE_DATASET_KEYS.includes(key)
);

const state = {
  brushes: [],
  strokes: [],
  history: [],
  redoHistory: [],
  camera: { x: 0, y: 0, scale: 1 },
  drawing: null,
  placementTask: null,
  sequenceExportActive: false,
  erasing: null,
  panning: null,
  touchPointers: new Map(),
  touchGesture: null,
  drawMode: "pencil",
  shapeDraft: null,
  editLayerDrag: null,
  editLayerMove: null,
  sequenceRafId: null,
  selectedEditLayerId: null,
  strokeById: new Map(),
  stampSpatialBuckets: new Map(),
  stampSpatialCells: new WeakMap(),
  stampCount: 0,
  stampVisibilityRafId: null,
  urlRefCounts: new Map(),
  nextBrushId: 1,
  nextStrokeId: 1,
  saveTimerId: null,
  soloBrushId: null,
  selectedBrushIds: new Set(),
  favoriteBrushSources: new Set(),
  favoriteReturnState: null,
  customBrushPresetSources: Array.from({ length: 5 }, () => new Set()),
  activeCustomBrushPresetIndex: null,
  activeStockBrushFolderId: null,
  stockBrushLoadingFolderId: null,
  gifAnimationsPaused: false,
  sidebarCollapsed: false,
  sidebarTab: "draw",
  previousSidebarTab: "draw",
  brushGalleryCollapsed: false,
  brushGallerySort: "alpha",
  savedCompositions: [],
  savedCompositionsLoaded: false,
  pendingSavedCompositionDeleteId: null,
  canvasBackgroundColor: "#ffffff",
  exportBackgroundEnabled: true,
  exportSeeBeyondEnabled: true,
  exportBgImageUrl: "",
  exportBgImageObjectUrl: "",
  exportBgImageOpacity: 100,
  exportBgImageMode: "stretch",
  exportBgImageTileSize: 128,
  exportBgImageNaturalWidth: 0,
  exportBgImageNaturalHeight: 0,
  exportBgImagePreviewUrl: "",
  showGifCountIndicator: true,
  showGifPauseButton: true,
  showDrawBackgroundColorControl: false,
  brushPreviewEnabled: true,
  eraseMode: false,
  pointerInViewport: false,
  lastPointerClientX: 0,
  lastPointerClientY: 0,
  cursorTrailEntries: [],
  cursorTrailLastWorldX: null,
  cursorTrailLastWorldY: null,
  exportMode: false,
  exportTask: null,
  lastExportSetup: null,
  exportAnimationAuto: true,
  exportAnimationSeconds: 3,
  exportAnimationFrameCount: "",
  exportVideoAuto: true,
  exportVideoSeconds: 3,
  exportSelectionBounds: null,
  exportScalePercent: 100,
  exportDrag: null,
  ctrlOrMetaHeld: false,
  shortcutPreview: {
    brushId: null,
    hideTimerId: null
  },
  brushCursorPreview: {
    brushId: null,
    sourceUrl: "",
    frozenUrl: "",
    loadingUrl: "",
    failedUrl: "",
    renderedUrl: "",
    loadToken: 0
  },
  eraseCursorRafId: null,
  eraseCursorRadiusScreen: 9,
  rotationIndicatorDrag: null,
  collapsedSliderGroups: {},
  tintPopoverOpen: false,
  brushCropEditor: {
    open: false,
    brushId: null,
    imageUrl: "",
    imageWidth: 0,
    imageHeight: 0,
    outputWidth: 0,
    outputHeight: 0,
    frameCount: 0,
    frameStart: 0,
    frameEnd: 0,
    frameDrag: null,
    frameAnimation: null,
    frameControlsLoading: false,
    framePreviewUrls: [],
    framePreviewTimerId: null,
    framePreviewIndex: 0,
    weightMode: "normal",
    cropRect: null,
    drag: null
  }
};

let snapshotDbPromise = null;
let sessionTabIdCache = null;
let gifLibraryPromise = null;
let gifuctModulePromise = null;
let tintNativePickerOpen = false;
let canvasBgNativePickerOpen = false;
let suppressTintPickerClick = false;

function createCancellationError(message = "Operation cancelled.") {
  const error = new Error(message);
  error.name = "AbortError";
  return error;
}

function isCancellationError(error) {
  return error && error.name === "AbortError";
}

function createCancellableTask(type) {
  return {
    type,
    cancelled: false,
    gif: null,
    mediaRecorder: null,
    cancel() {
      this.cancelled = true;
      if (this.gif && typeof this.gif.abort === "function") {
        try {
          this.gif.abort();
        } catch (error) {
          // GIF may already have finished or aborted.
        }
      }
      if (this.mediaRecorder && this.mediaRecorder.state !== "inactive") {
        try {
          this.mediaRecorder.stop();
        } catch (error) {
          // Recorder may already have stopped.
        }
      }
    }
  };
}

function throwIfTaskCancelled(task) {
  if (task && task.cancelled) {
    throw createCancellationError();
  }
}

async function yieldToMainThread(task = null) {
  await new Promise((resolve) => window.setTimeout(resolve, 0));
  throwIfTaskCancelled(task);
}

async function waitForExportFrameDelay(durationMs, task = null) {
  await new Promise((resolve) => window.setTimeout(resolve, Math.max(0, Number(durationMs) || 0)));
  throwIfTaskCancelled(task);
}

function setExportButtonContent(text, loading = false, button = exportButton) {
  if (!button) {
    return;
  }
  button.replaceChildren();
  if (!loading) {
    button.textContent = text;
    return;
  }

  const spinner = document.createElement("span");
  spinner.className = "export-loading-spinner";
  spinner.setAttribute("aria-hidden", "true");

  const label = document.createElement("span");
  label.className = "export-loading-label";
  label.textContent = text;

  button.appendChild(spinner);
  button.appendChild(label);
}

function updateExportProgress(task, percent, label = "Exporting") {
  if (!task || state.exportTask !== task) {
    return;
  }
  const button = task.button || exportButton;
  const progress = clamp(Math.round(Number(percent) || 0), 0, 100);
  const displayLabel = task.cancelled ? "Cancelling export" : label;
  task.progress = progress;
  task.progressLabel = displayLabel;
  button.style.setProperty("--export-progress", `${progress}%`);
  setExportButtonContent(`${displayLabel} ${progress}%`, true, button);
  button.setAttribute("aria-label", `${displayLabel} ${progress}%`);
  button.title = `${displayLabel} ${progress}%`;
}

function resetExportProgress(button = exportButton, label = "Render GIF") {
  if (!button) {
    return;
  }
  button.style.removeProperty("--export-progress");
  setExportButtonContent(label, false, button);
}

function cancelPlacementTask() {
  if (!state.placementTask) {
    return false;
  }
  state.placementTask.cancel();
  updateBrushStatus("Cancelling placement...");
  return true;
}

function cancelExportTask() {
  if (!state.exportTask) {
    return false;
  }
  state.exportTask.cancel();
  updateExportModeUI();
  updateBrushStatus("Cancelling export...");
  return true;
}
let suppressNextTintInputClick = false;
let suppressNextCanvasBgInputClick = false;
const tintFilterCache = new Map();
let exportTintScratchCanvas = null;
const exportBackgroundImageCache = new Map();
const exportBackgroundAnimationCache = new Map();
const exportBackgroundStillPreviewCache = new Map();
const exportBackgroundRenderCache = new Map();
const brushSourceDataCache = new Map();
const stockBrushIconPaths = new Map();
const brushFrameCountPromises = new Map();
const brushFrameCountQueue = [];
let activeBrushFrameCountDecodes = 0;
const NO_TINT_SETTINGS = { color: "#ffffff", amountPercent: 0 };
const gifPauseObserver = new MutationObserver((mutations) => {
  if (!state.gifAnimationsPaused) {
    return;
  }

  for (const mutation of mutations) {
    for (const node of mutation.addedNodes) {
      applyGifPauseStateToNode(node);
    }
  }
});

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

function getNormalizedWheelDelta(event) {
  let delta = Number(event.deltaY) || 0;
  if (event.deltaMode === 1) {
    delta *= 16;
  } else if (event.deltaMode === 2) {
    delta *= window.innerHeight;
  }
  return delta;
}

function isRotationWheelShortcutActive(event) {
  const modifierFromState =
    typeof event.getModifierState === "function"
      ? event.getModifierState("Control") || event.getModifierState("Meta")
      : false;
  return Boolean(event.ctrlKey || event.metaKey || modifierFromState || state.ctrlOrMetaHeld) &&
    !event.altKey;
}

function normalizeHexColor(color, fallback = "#ffffff") {
  if (typeof color !== "string") {
    return fallback;
  }

  const trimmed = color.trim().toLowerCase();
  if (!trimmed.startsWith("#")) {
    return fallback;
  }

  if (/^#[0-9a-f]{3}$/i.test(trimmed)) {
    return `#${trimmed[1]}${trimmed[1]}${trimmed[2]}${trimmed[2]}${trimmed[3]}${trimmed[3]}`;
  }

  if (/^#[0-9a-f]{6}$/i.test(trimmed)) {
    return trimmed;
  }

  return fallback;
}

function hexToRgbUnit(hexColor) {
  const normalized = normalizeHexColor(hexColor);
  const red = parseInt(normalized.slice(1, 3), 16) / 255;
  const green = parseInt(normalized.slice(3, 5), 16) / 255;
  const blue = parseInt(normalized.slice(5, 7), 16) / 255;
  return { red, green, blue };
}

function normalizeTintSettings(tintSettings = null, fallbackTintSettings = null) {
  const fallbackColor = normalizeHexColor(
    fallbackTintSettings && typeof fallbackTintSettings.color === "string"
      ? fallbackTintSettings.color
      : "#ffffff",
    "#ffffff"
  );
  const fallbackAmount = clamp(
    Number.isFinite(Number(fallbackTintSettings?.amountPercent))
      ? Number(fallbackTintSettings.amountPercent)
      : 0,
    0,
    100
  );

  const color = normalizeHexColor(
    tintSettings && typeof tintSettings.color === "string" ? tintSettings.color : fallbackColor,
    fallbackColor
  );
  const amountPercent = clamp(
    Number.isFinite(Number(tintSettings?.amountPercent))
      ? Number(tintSettings.amountPercent)
      : fallbackAmount,
    0,
    100
  );

  return { color, amountPercent };
}

function getTintLayerList(tintSettings = null, fallbackTintSettings = null) {
  const source = tintSettings == null && fallbackTintSettings != null
    ? fallbackTintSettings
    : tintSettings;
  const rawLayers = Array.isArray(source?.layers) ? source.layers : [source];
  return rawLayers
    .map((layer) => normalizeTintSettings(layer, fallbackTintSettings))
    .filter((layer) => layer.amountPercent > 0);
}

function createLayeredTintSettings(...tintSettingsList) {
  const layers = [];
  for (const tintSettings of tintSettingsList) {
    layers.push(...getTintLayerList(tintSettings));
  }

  if (!layers.length) {
    return NO_TINT_SETTINGS;
  }

  if (layers.length === 1) {
    return layers[0];
  }

  return { layers };
}

function getCurrentTintSettings() {
  return normalizeTintSettings({
    color: tintColorInput ? tintColorInput.value : "#ffffff",
    amountPercent: tintAmountSlider ? parseNumericInputValue(tintAmountSlider, 0) : 0
  });
}

function getTintMatrixValues(tintSettings) {
  const layers = getTintLayerList(tintSettings);
  let keep = 1;
  let redOffset = 0;
  let greenOffset = 0;
  let blueOffset = 0;

  for (const layer of layers) {
    const amount = layer.amountPercent / 100;
    const color = hexToRgbUnit(layer.color);
    const layerKeep = 1 - amount;
    redOffset = redOffset * layerKeep + amount * color.red;
    greenOffset = greenOffset * layerKeep + amount * color.green;
    blueOffset = blueOffset * layerKeep + amount * color.blue;
    keep *= layerKeep;
  }

  // Apply tint layers in order so sequence color effects stack on top of brush tint.
  return [
    keep, 0, 0, 0, redOffset,
    0, keep, 0, 0, greenOffset,
    0, 0, keep, 0, blueOffset,
    0, 0, 0, 1, 0
  ];
}

function getTintFilterId(tintSettings) {
  const layers = getTintLayerList(tintSettings);
  if (!layers.length) {
    return "";
  }

  const key = layers
    .map((layer) => {
      const colorToken = layer.color.replace("#", "");
      const amountToken = String(layer.amountPercent).replace(/[^0-9a-z]+/gi, "_");
      return `${colorToken}-${amountToken}`;
    })
    .join("__");
  const cachedFilterId = tintFilterCache.get(key);
  if (cachedFilterId) {
    return cachedFilterId;
  }

  const filterId = `brushTintFilter-${key}`;
  const existingFilter = document.getElementById(filterId);
  if (existingFilter) {
    tintFilterCache.set(key, filterId);
    return filterId;
  }

  const defs = filterDefs ? filterDefs.querySelector("defs") : null;
  if (!defs) {
    return "";
  }

  const svgNamespace = "http://www.w3.org/2000/svg";
  const filterElement = document.createElementNS(svgNamespace, "filter");
  filterElement.setAttribute("id", filterId);
  filterElement.setAttribute("color-interpolation-filters", "sRGB");

  const colorMatrix = document.createElementNS(svgNamespace, "feColorMatrix");
  colorMatrix.setAttribute("type", "matrix");
  const matrixValues = getTintMatrixValues({ layers });
  colorMatrix.setAttribute("values", matrixValues.map((value) => value.toFixed(6)).join(" "));

  filterElement.appendChild(colorMatrix);
  defs.appendChild(filterElement);
  tintFilterCache.set(key, filterId);
  return filterId;
}

function getBrushTintCssFilter(disabled = false, tintSettings = null) {
  const normalized = tintSettings == null ? getCurrentTintSettings() : tintSettings;
  if (!getTintLayerList(normalized).length) {
    return disabled ? "grayscale(0.75)" : "";
  }

  const filterId = getTintFilterId(normalized);
  if (!filterId) {
    return disabled ? "grayscale(0.75)" : "";
  }

  const tintFilter = `url(#${filterId})`;
  return disabled ? `grayscale(0.75) ${tintFilter}` : tintFilter;
}

function applyBrushTintStyle(element, disabled = false, tintSettings = null) {
  if (!element) {
    return;
  }
  const filterValue = getBrushTintCssFilter(disabled, tintSettings);
  if (filterValue) {
    element.style.filter = filterValue;
  } else {
    element.style.removeProperty("filter");
  }
}

function setElementTintData(element, tintSettings) {
  if (!element || !element.dataset) {
    return;
  }
  const normalized = normalizeTintSettings(tintSettings, getCurrentTintSettings());
  element.dataset.tintColor = normalized.color;
  element.dataset.tintAmount = String(normalized.amountPercent);
}

function updateBrushTintMatrix() {
  getTintFilterId(getCurrentTintSettings());
}

function refreshBrushTintOnVisibleElements() {
  const currentTint = getCurrentTintSettings();

  if (shortcutPreview.classList.contains("is-visible")) {
    applyBrushTintStyle(shortcutPreview, false, currentTint);
  }

  if (brushCursorPreview && brushCursorPreview.classList.contains("is-visible")) {
    applyBrushTintStyle(brushCursorPreview, false, currentTint);
  }

  const thumbs = brushGallery.querySelectorAll(".brush-thumb");
  for (const thumb of thumbs) {
    const card = thumb.closest(".brush-item");
    const disabled = Boolean(card && card.classList.contains("is-disabled"));
    applyBrushTintStyle(thumb, disabled, NO_TINT_SETTINGS);
  }
}

function updateTintControlUI() {
  if (!tintColorInput || !tintSwatch || !tintAmountValue || !tintAmountSlider) {
    return;
  }
  const normalizedColor = normalizeHexColor(tintColorInput.value);
  tintColorInput.value = normalizedColor;
  tintSwatch.style.background = normalizedColor;
  tintAmountValue.textContent = String(parseNumericInputValue(tintAmountSlider, 0));
}

function isNativeTintPickerActive() {
  return Boolean(
    tintNativePickerOpen ||
      (tintColorInput && document.activeElement === tintColorInput)
  );
}

function closeNativeTintPicker() {
  if (!tintColorInput) {
    return;
  }
  tintNativePickerOpen = false;
  tintColorInput.blur();
}

function openNativeTintPicker() {
  if (!tintColorInput) {
    return false;
  }

  if (typeof tintColorInput.showPicker === "function") {
    try {
      tintColorInput.showPicker();
      tintNativePickerOpen = true;
      return true;
    } catch (error) {
      // Fall through for browsers that block showPicker.
    }
  }

  // Fallback path for browsers without showPicker support.
  // Do not force tintNativePickerOpen here; rely on focus/blur to reflect true state.
  tintColorInput.focus();
  tintColorInput.click();
  return true;
}

function isCanvasBgPickerActive() {
  return Boolean(
    canvasBgNativePickerOpen ||
      (drawCanvasBgColorInput && document.activeElement === drawCanvasBgColorInput) ||
      (canvasBgColorInput && document.activeElement === canvasBgColorInput)
  );
}

function closeCanvasBgPicker() {
  canvasBgNativePickerOpen = false;
  if (drawCanvasBgColorInput) {
    drawCanvasBgColorInput.blur();
  }
  if (canvasBgColorInput) {
    canvasBgColorInput.blur();
  }
}

function setTintPopoverOpen(nextOpen) {
  if (!tintPopover || !tintPickerButton) {
    return;
  }
  state.tintPopoverOpen = Boolean(nextOpen);
  tintPopover.hidden = !state.tintPopoverOpen;
  tintPickerButton.setAttribute("aria-expanded", String(state.tintPopoverOpen));
  if (!state.tintPopoverOpen) {
    closeNativeTintPicker();
  }
}

function applyTintSettingsFromInputs() {
  updateTintControlUI();
  updateBrushTintMatrix();
  refreshBrushTintOnVisibleElements();
}

function isGifUrl(url) {
  if (typeof url !== "string") {
    return false;
  }
  return /^data:image\/gif/i.test(url) || /\.gif(?:$|[?#])/i.test(url);
}

function getBrushSourceIsGif(brush) {
  if (!brush) {
    return false;
  }
  return (
    isGifUrl(brush.url) ||
    isGifUrl(brush.originalUrl) ||
    /\.gif$/i.test(String(brush.name || ""))
  );
}

function normalizeBrushFrameCount(value) {
  const count = Number(value);
  return Number.isFinite(count) && count > 0 ? Math.max(1, Math.round(count)) : null;
}

function getBrushFrameCountLabel(brush) {
  const count = normalizeBrushFrameCount(brush?.frameCount);
  if (count) {
    return count === 1 ? "1 frame" : `${count} frames`;
  }
  return getBrushSourceIsGif(brush) ? "... frames" : "1 frame";
}

function getBrushDimensionsLabel(brush) {
  const width = Math.max(1, Math.round(Number(brush?.originalWidth) || Number(brush?.width) || 1));
  const height = Math.max(1, Math.round(Number(brush?.originalHeight) || Number(brush?.height) || 1));
  return `${width}x${height}`;
}

function getBrushMetaText(brush) {
  return `${getBrushFrameCountLabel(brush)} / ${getBrushDimensionsLabel(brush)}`;
}

function clearBrushFrameCountJobs() {
  brushFrameCountPromises.clear();
  brushFrameCountQueue.length = 0;
}

function runBrushFrameCountQueue() {
  while (
    activeBrushFrameCountDecodes < BRUSH_FRAME_COUNT_DECODE_CONCURRENCY &&
    brushFrameCountQueue.length
  ) {
    const job = brushFrameCountQueue.shift();
    activeBrushFrameCountDecodes += 1;

    window.setTimeout(() => {
      decodeGifAnimation(job.sourceUrl)
        .then((animation) => normalizeBrushFrameCount(animation?.frames?.length) || 1)
        .catch(() => 1)
        .then((count) => {
          const currentBrush = findBrushById(job.brushId);
          if (!currentBrush || (currentBrush.originalUrl || currentBrush.url) !== job.sourceUrl) {
            return;
          }
          currentBrush.frameCount = count;
          if (state.sidebarTab === "brushes") {
            renderBrushGallery();
          }
          scheduleSessionSave();
        })
        .finally(() => {
          brushFrameCountPromises.delete(job.brushId);
          activeBrushFrameCountDecodes = Math.max(0, activeBrushFrameCountDecodes - 1);
          runBrushFrameCountQueue();
        });
    }, 0);
  }
}

function ensureBrushFrameCount(brush) {
  if (!brush || !getBrushSourceIsGif(brush)) {
    if (brush && !normalizeBrushFrameCount(brush.frameCount)) {
      brush.frameCount = 1;
    }
    return;
  }

  if (normalizeBrushFrameCount(brush.frameCount)) {
    return;
  }

  const brushId = Number(brush.id);
  if (!Number.isFinite(brushId) || brushFrameCountPromises.has(brushId)) {
    return;
  }

  const sourceUrl = brush.originalUrl || brush.url;
  brushFrameCountPromises.set(brushId, true);
  brushFrameCountQueue.push({ brushId, sourceUrl });
  runBrushFrameCountQueue();
}

function getImageGifSource(image) {
  if (!(image instanceof HTMLImageElement)) {
    return "";
  }

  return (
    image.dataset.gifPausedSrc ||
    image.getAttribute("src") ||
    image.currentSrc ||
    image.dataset.brushUrl ||
    ""
  );
}

function markGifPlaybackStart(image, source = "") {
  if (!(image instanceof HTMLImageElement)) {
    return;
  }
  const gifSource = source || getImageGifSource(image);
  if (!isGifUrl(gifSource)) {
    delete image.dataset.gifPlaybackSource;
    delete image.dataset.gifPlaybackStartedAt;
    return;
  }
  if (image.dataset.gifPlaybackSource !== gifSource || !Number.isFinite(Number(image.dataset.gifPlaybackStartedAt))) {
    image.dataset.gifPlaybackSource = gifSource;
    image.dataset.gifPlaybackStartedAt = String(performance.now());
  }
}

function isViewportCulledStamp(image) {
  return image instanceof HTMLImageElement && image.dataset.viewportCulled === "true";
}

function isImageLayerPaused(image) {
  if (!(image instanceof HTMLImageElement) || !image.classList.contains("stamp")) {
    return false;
  }
  const strokeId = Number(image.dataset.strokeId);
  const stroke = Number.isFinite(strokeId) ? state.strokeById.get(strokeId) : null;
  return Boolean(stroke?.animationPaused);
}

function shouldPauseGifImage(image) {
  return state.gifAnimationsPaused || isImageLayerPaused(image);
}

function isStrokeSequencePaused(stroke) {
  return Boolean(state.gifAnimationsPaused || stroke?.animationPaused);
}

function captureImageStillFrame(image) {
  const width = Math.max(1, image.naturalWidth || image.width || 1);
  const height = Math.max(1, image.naturalHeight || image.height || 1);
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  const ctx = canvas.getContext("2d", { alpha: true });
  if (!ctx) {
    return "";
  }
  ctx.drawImage(image, 0, 0, width, height);
  return canvas.toDataURL("image/png");
}

function freezeGifImage(image) {
  if (
    !(image instanceof HTMLImageElement) ||
    image.dataset.gifPausedSrc ||
    isViewportCulledStamp(image)
  ) {
    return;
  }

  const source = getImageGifSource(image);
  if (!isGifUrl(source)) {
    return;
  }
  if (!image.complete || !image.naturalWidth || !image.naturalHeight) {
    if (image.dataset.gifPausePending) {
      return;
    }
    image.dataset.gifPausePending = "true";
    image.addEventListener(
      "load",
      () => {
        delete image.dataset.gifPausePending;
        if (shouldPauseGifImage(image)) {
          freezeGifImage(image);
        }
      },
      { once: true }
    );
    return;
  }

  try {
    const stillFrameUrl = captureImageStillFrame(image);
    if (!stillFrameUrl) {
      return;
    }
    image.dataset.gifPausedSrc = image.getAttribute("src") || source;
    image.src = stillFrameUrl;
  } catch (error) {
    // If the image cannot be captured, leave it animated rather than breaking it.
  }
}

function resumeGifImage(image) {
  if (!(image instanceof HTMLImageElement)) {
    return;
  }

  delete image.dataset.gifPausePending;
  const pausedSource = image.dataset.gifPausedSrc;
  if (!pausedSource) {
    return;
  }

  image.src = pausedSource;
  markGifPlaybackStart(image, pausedSource);
  delete image.dataset.gifPausedSrc;
}

function applyGifPauseStateToImage(image) {
  if (shouldPauseGifImage(image)) {
    freezeGifImage(image);
  } else {
    markGifPlaybackStart(image);
  }
}

function applyBrushGalleryPreviewAnimationState(preview, brush) {
  if (!(preview instanceof HTMLImageElement)) {
    return;
  }

  if (brush && brush.enabled === false) {
    preview.dataset.forceGifStill = "true";
    freezeGifImage(preview);
    return;
  }

  delete preview.dataset.forceGifStill;
  applyGifPauseStateToImage(preview);
}

function applyGifPauseStateToNode(node) {
  if (!(node instanceof Element)) {
    return;
  }

  if (node instanceof HTMLImageElement) {
    if (node.dataset.forceGifStill === "true") {
      freezeGifImage(node);
      return;
    }
    applyGifPauseStateToImage(node);
  }

  const images = node.querySelectorAll("img");
  for (const image of images) {
    if (image.dataset.forceGifStill === "true") {
      freezeGifImage(image);
      continue;
    }
    applyGifPauseStateToImage(image);
  }
}

function updateGifPauseButtonUI() {
  gifPauseButton.hidden = state.showGifPauseButton === false;
  gifPauseButton.classList.toggle("is-paused", state.gifAnimationsPaused);
  gifPauseButton.setAttribute("aria-pressed", String(state.gifAnimationsPaused));
  gifPauseButton.setAttribute(
    "aria-label",
    state.gifAnimationsPaused ? "Resume GIF animations" : "Pause GIF animations"
  );
  gifPauseButton.title = state.gifAnimationsPaused
    ? "Resume GIF animations"
    : "Pause GIF animations";
  updateGifPauseButtonPosition();
}

function updateGifPauseButtonPosition() {
  if (!gifPauseButton) {
    return;
  }

  const baseLeft = 14;
  const gap = 10;
  const shouldFollowCounter =
    gifCountIndicator &&
    state.showGifCountIndicator !== false &&
    !gifCountIndicator.hidden;

  if (!shouldFollowCounter) {
    gifPauseButton.style.left = `${baseLeft}px`;
    return;
  }

  const rect = gifCountIndicator.getBoundingClientRect();
  gifPauseButton.style.left = `${Math.round(rect.right + gap)}px`;
}

function setGifAnimationsPaused(paused) {
  state.gifAnimationsPaused = Boolean(paused);
  applyGlobalGifPauseState(state.gifAnimationsPaused);
  updateGifPauseButtonUI();
}

function loadGifLibrary() {
  if (typeof window.GIF === "function") {
    return Promise.resolve();
  }
  if (gifLibraryPromise) {
    return gifLibraryPromise;
  }

  gifLibraryPromise = new Promise((resolve, reject) => {
    const existingScript = Array.from(document.querySelectorAll("script")).find((scriptElement) => {
      const rawSrc = scriptElement.getAttribute("src") || "";
      return rawSrc === GIF_JS_LIBRARY_URL || rawSrc.endsWith(`/${GIF_JS_LIBRARY_URL}`);
    });
    if (existingScript) {
      existingScript.addEventListener("load", () => resolve(), { once: true });
      existingScript.addEventListener(
        "error",
        () => reject(new Error("Failed to load GIF encoder.")),
        { once: true }
      );
      return;
    }

    const script = document.createElement("script");
    script.src = GIF_JS_LIBRARY_URL;
    script.async = true;
    script.onload = () => resolve();
    script.onerror = () => reject(new Error("Failed to load GIF encoder."));
    document.head.appendChild(script);
  });

  return gifLibraryPromise;
}

function loadGifuctModule() {
  if (gifuctModulePromise) {
    return gifuctModulePromise;
  }

  gifuctModulePromise = import(GIFUCT_MODULE_URL).then((module) => {
    if (
      !module ||
      typeof module.parseGIF !== "function" ||
      typeof module.decompressFrames !== "function"
    ) {
      throw new Error("GIF decoder module is unavailable.");
    }
    return module;
  });

  return gifuctModulePromise;
}

function dataUrlToUint8Array(url) {
  const markerIndex = url.indexOf(",");
  if (markerIndex < 0) {
    throw new Error("Invalid data URL.");
  }
  const metadata = url.slice(0, markerIndex);
  const payload = url.slice(markerIndex + 1);

  if (metadata.includes(";base64")) {
    const binary = atob(payload);
    const bytes = new Uint8Array(binary.length);
    for (let index = 0; index < binary.length; index += 1) {
      bytes[index] = binary.charCodeAt(index);
    }
    return bytes;
  }

  const text = decodeURIComponent(payload);
  const bytes = new Uint8Array(text.length);
  for (let index = 0; index < text.length; index += 1) {
    bytes[index] = text.charCodeAt(index) & 0xff;
  }
  return bytes;
}

async function readImageBytes(url) {
  if (typeof url !== "string" || !url) {
    throw new Error("Missing image URL.");
  }

  if (url.startsWith("data:")) {
    return dataUrlToUint8Array(url);
  }

  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to fetch image bytes (${response.status}).`);
  }
  const buffer = await response.arrayBuffer();
  return new Uint8Array(buffer);
}

function getBrushOriginalWidth(brush) {
  return Math.max(1, Number(brush?.originalWidth) || Number(brush?.width) || 1);
}

function getBrushOriginalHeight(brush) {
  return Math.max(1, Number(brush?.originalHeight) || Number(brush?.height) || 1);
}

function getBrushOriginalUrl(brush) {
  if (typeof brush?.originalUrl === "string" && brush.originalUrl) {
    return brush.originalUrl;
  }
  return typeof brush?.url === "string" ? brush.url : "";
}

function normalizeBrushCropRect(rect, fullWidth, fullHeight) {
  const widthLimit = Math.max(BRUSH_CROP_MIN_SIZE, Math.round(fullWidth));
  const heightLimit = Math.max(BRUSH_CROP_MIN_SIZE, Math.round(fullHeight));
  let x = Number(rect?.x);
  let y = Number(rect?.y);
  let width = Number(rect?.width);
  let height = Number(rect?.height);

  if (!Number.isFinite(x)) {
    x = 0;
  }
  if (!Number.isFinite(y)) {
    y = 0;
  }
  if (!Number.isFinite(width)) {
    width = widthLimit;
  }
  if (!Number.isFinite(height)) {
    height = heightLimit;
  }

  width = Math.max(BRUSH_CROP_MIN_SIZE, Math.min(width, widthLimit));
  height = Math.max(BRUSH_CROP_MIN_SIZE, Math.min(height, heightLimit));
  x = clamp(x, 0, Math.max(0, widthLimit - width));
  y = clamp(y, 0, Math.max(0, heightLimit - height));

  return {
    x: Math.round(x),
    y: Math.round(y),
    width: Math.round(width),
    height: Math.round(height)
  };
}

function getBrushCurrentCropRect(brush) {
  const fullWidth = getBrushOriginalWidth(brush);
  const fullHeight = getBrushOriginalHeight(brush);
  if (
    brush?.cropRect &&
    Number.isFinite(Number(brush.cropRect.width)) &&
    Number.isFinite(Number(brush.cropRect.height))
  ) {
    return normalizeBrushCropRect(brush.cropRect, fullWidth, fullHeight);
  }
  return {
    x: 0,
    y: 0,
    width: fullWidth,
    height: fullHeight
  };
}

function isFullBrushCropRect(rect, fullWidth, fullHeight) {
  const normalized = normalizeBrushCropRect(rect, fullWidth, fullHeight);
  return (
    normalized.x <= 0 &&
    normalized.y <= 0 &&
    normalized.width >= fullWidth &&
    normalized.height >= fullHeight
  );
}

function normalizeBrushFrameRange(range, frameCount) {
  const count = Math.max(0, Math.floor(Number(frameCount) || 0));
  if (count <= 0) {
    return null;
  }

  let start = Math.floor(Number(range?.start));
  let end = Math.floor(Number(range?.end));
  if (!Number.isFinite(start)) {
    start = 0;
  }
  if (!Number.isFinite(end)) {
    end = count;
  }

  start = clamp(start, 0, Math.max(0, count - 1));
  end = clamp(end, start + 1, count);
  return { start, end };
}

function isFullBrushFrameRange(range, frameCount) {
  const normalized = normalizeBrushFrameRange(range, frameCount);
  const count = Math.max(0, Math.floor(Number(frameCount) || 0));
  return !normalized || normalized.start <= 0 && normalized.end >= count;
}

function getBrushCropAspectRatio() {
  const rect = state.brushCropEditor.cropRect || {};
  const width = Math.max(1, Number(rect.width) || Number(state.brushCropEditor.imageWidth) || 1);
  const height = Math.max(1, Number(rect.height) || Number(state.brushCropEditor.imageHeight) || 1);
  return width / height;
}

function setBrushCropOutputSize(width, height) {
  state.brushCropEditor.outputWidth = clamp(Math.round(Number(width) || 1), 1, EXPORT_MAX_DIMENSION);
  state.brushCropEditor.outputHeight = clamp(Math.round(Number(height) || 1), 1, EXPORT_MAX_DIMENSION);
}

function normalizeBrushWeightMode(weightMode) {
  const mode = String(weightMode || "normal").toLowerCase();
  if (Object.prototype.hasOwnProperty.call(BRUSH_WEIGHT_MULTIPLIERS, mode)) {
    if (mode === "low") {
      return "uncommon";
    }
    if (mode === "high") {
      return "common";
    }
    return mode;
  }
  return "normal";
}

function updateBrushCropProbabilityUI() {
  const activeMode = normalizeBrushWeightMode(state.brushCropEditor.weightMode);
  for (const button of brushCropProbabilityButtons) {
    const isActive = normalizeBrushWeightMode(button.dataset.weightMode) === activeMode;
    button.classList.toggle("is-active", isActive);
    button.setAttribute("aria-pressed", String(isActive));
  }
}

function syncBrushCropOutputToAspect(axis = "width") {
  const aspectRatio = getBrushCropAspectRatio();
  if (axis === "height") {
    const height = Math.max(1, Number(state.brushCropEditor.outputHeight) || 1);
    setBrushCropOutputSize(height * aspectRatio, height);
    return;
  }

  const width = Math.max(1, Number(state.brushCropEditor.outputWidth) || 1);
  setBrushCropOutputSize(width, width / aspectRatio);
}

function getBrushCropNativeOutputSize() {
  const rect = state.brushCropEditor.cropRect || {};
  return {
    width: Math.max(1, Math.round(Number(rect.width) || Number(state.brushCropEditor.imageWidth) || 1)),
    height: Math.max(1, Math.round(Number(rect.height) || Number(state.brushCropEditor.imageHeight) || 1))
  };
}

function updateBrushCropResolutionInputs() {
  if (!brushCropWidthInput || !brushCropHeightInput) {
    return;
  }
  brushCropWidthInput.value = String(Math.max(1, Math.round(Number(state.brushCropEditor.outputWidth) || 1)));
  brushCropHeightInput.value = String(Math.max(1, Math.round(Number(state.brushCropEditor.outputHeight) || 1)));
  if (brushCropResolutionResetButton) {
    const nativeSize = getBrushCropNativeOutputSize();
    const outputWidth = Math.max(1, Math.round(Number(state.brushCropEditor.outputWidth) || 1));
    const outputHeight = Math.max(1, Math.round(Number(state.brushCropEditor.outputHeight) || 1));
    brushCropResolutionResetButton.hidden =
      outputWidth === nativeSize.width && outputHeight === nativeSize.height;
  }
}

function updateBrushCropFrameControls() {
  if (
    !brushCropFrameControls ||
    !brushCropFrameSegments ||
    !brushCropFrameSelection ||
    !brushCropFrameStartHandle ||
    !brushCropFrameEndHandle
  ) {
    return;
  }

  const frameCount = Math.max(0, Math.floor(Number(state.brushCropEditor.frameCount) || 0));
  const isGifEditor = getBrushSourceIsGif({
    url: state.brushCropEditor.imageUrl,
    originalUrl: state.brushCropEditor.imageUrl
  });
  const showLoadingTrack = isGifEditor && state.brushCropEditor.frameControlsLoading;
  brushCropFrameControls.hidden = frameCount <= 1 && !showLoadingTrack;
  if (frameCount <= 1) {
    if (showLoadingTrack) {
      if (brushCropFrameSegments.dataset.frameCount !== "loading") {
        brushCropFrameSegments.dataset.frameCount = "loading";
        brushCropFrameSegments.innerHTML = "";
      }
      brushCropFrameSelection.style.left = "0%";
      brushCropFrameSelection.style.width = "100%";
      brushCropFrameStartHandle.hidden = true;
      brushCropFrameEndHandle.hidden = true;
      if (brushCropFrameReadout) {
        brushCropFrameReadout.textContent = "loading frames...";
      }
    }
    return;
  }
  brushCropFrameStartHandle.hidden = false;
  brushCropFrameEndHandle.hidden = false;

  const range = normalizeBrushFrameRange(
    { start: state.brushCropEditor.frameStart, end: state.brushCropEditor.frameEnd },
    frameCount
  ) || { start: 0, end: frameCount };
  state.brushCropEditor.frameStart = range.start;
  state.brushCropEditor.frameEnd = range.end;

  if (Number(brushCropFrameSegments.dataset.frameCount) !== frameCount) {
    brushCropFrameSegments.dataset.frameCount = String(frameCount);
    brushCropFrameSegments.innerHTML = "";
    const fragment = document.createDocumentFragment();
    for (let index = 0; index < frameCount; index += 1) {
      const segment = document.createElement("span");
      segment.className = "brush-crop-frame-segment";
      fragment.appendChild(segment);
    }
    brushCropFrameSegments.appendChild(fragment);
  }

  const startPercent = (range.start / frameCount) * 100;
  const endPercent = (range.end / frameCount) * 100;
  brushCropFrameSelection.style.left = `${startPercent}%`;
  brushCropFrameSelection.style.width = `${Math.max(0, endPercent - startPercent)}%`;
  brushCropFrameStartHandle.style.left = `${startPercent}%`;
  brushCropFrameEndHandle.style.left = `${endPercent}%`;
  brushCropFrameStartHandle.setAttribute("aria-valuenow", String(range.start + 1));
  brushCropFrameEndHandle.setAttribute("aria-valuenow", String(range.end));
  if (brushCropFrameReadout) {
    brushCropFrameReadout.textContent = `frames ${range.start + 1}-${range.end} / ${frameCount}`;
  }
}

function updateBrushCropFrameRangeFromPointer(clientX, edge) {
  const frameCount = Math.max(0, Math.floor(Number(state.brushCropEditor.frameCount) || 0));
  if (!brushCropFrameTrack || frameCount <= 1) {
    return;
  }

  const rect = brushCropFrameTrack.getBoundingClientRect();
  const ratio = rect.width > 0 ? clamp((clientX - rect.left) / rect.width, 0, 1) : 0;
  const frame = clamp(Math.round(ratio * frameCount), 0, frameCount);
  if (edge === "start") {
    state.brushCropEditor.frameStart = clamp(frame, 0, Math.max(0, state.brushCropEditor.frameEnd - 1));
  } else {
    state.brushCropEditor.frameEnd = clamp(frame, state.brushCropEditor.frameStart + 1, frameCount);
  }
  updateBrushCropFrameControls();
  startBrushCropFramePreview();
}

function clearBrushCropFramePreviewTimer() {
  const timerId = state.brushCropEditor.framePreviewTimerId;
  if (timerId !== null) {
    window.clearTimeout(timerId);
  }
  state.brushCropEditor.framePreviewTimerId = null;
}

function getBrushCropFramePreviewUrl(index) {
  const animation = state.brushCropEditor.frameAnimation;
  const frames = Array.isArray(animation?.frames) ? animation.frames : [];
  const frame = frames[index];
  if (!frame) {
    return "";
  }

  if (state.brushCropEditor.framePreviewUrls[index]) {
    return state.brushCropEditor.framePreviewUrls[index];
  }

  try {
    const url = frame.toDataURL("image/png");
    state.brushCropEditor.framePreviewUrls[index] = url;
    return url;
  } catch (error) {
    return "";
  }
}

function startBrushCropFramePreview() {
  clearBrushCropFramePreviewTimer();
  if (!state.brushCropEditor.open || !brushCropImage) {
    return;
  }

  const animation = state.brushCropEditor.frameAnimation;
  const frames = Array.isArray(animation?.frames) ? animation.frames : [];
  const frameCount = frames.length;
  if (frameCount <= 1) {
    return;
  }

  const step = () => {
    if (!state.brushCropEditor.open) {
      return;
    }

    const range = normalizeBrushFrameRange(
      { start: state.brushCropEditor.frameStart, end: state.brushCropEditor.frameEnd },
      frameCount
    ) || { start: 0, end: frameCount };
    let index = Math.floor(Number(state.brushCropEditor.framePreviewIndex) || range.start);
    if (index < range.start || index >= range.end) {
      index = range.start;
    }

    const previewUrl = getBrushCropFramePreviewUrl(index);
    if (previewUrl) {
      delete brushCropImage.dataset.gifPausePending;
      delete brushCropImage.dataset.gifPausedSrc;
      brushCropImage.src = previewUrl;
    }

    const durations = Array.isArray(animation.durations) ? animation.durations : [];
    const delay = Math.max(
      20,
      Number.isFinite(Number(durations[index])) ? Number(durations[index]) : EXPORT_GIF_FRAME_DELAY_MS
    );
    state.brushCropEditor.framePreviewIndex = index + 1 >= range.end ? range.start : index + 1;
    state.brushCropEditor.framePreviewTimerId = window.setTimeout(step, delay);
  };

  step();
}

function readBlobAsDataUrl(blob) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(String(reader.result || ""));
    reader.onerror = () => reject(reader.error || new Error("Could not convert cropped image."));
    reader.readAsDataURL(blob);
  });
}

async function cropStaticImageToDataUrl(sourceUrl, cropRect) {
  const image = await new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.onerror = () => reject(new Error("Could not read source image for crop."));
    img.src = sourceUrl;
  });

  const canvas = document.createElement("canvas");
  canvas.width = Math.max(1, Math.round(cropRect.width));
  canvas.height = Math.max(1, Math.round(cropRect.height));
  const ctx = canvas.getContext("2d", { alpha: true });
  if (!ctx) {
    throw new Error("Could not create crop canvas.");
  }

  ctx.clearRect(0, 0, canvas.width, canvas.height);
  ctx.drawImage(
    image,
    cropRect.x,
    cropRect.y,
    cropRect.width,
    cropRect.height,
    0,
    0,
    canvas.width,
    canvas.height
  );
  return canvas.toDataURL("image/png");
}

async function cropAnimatedGifToDataUrl(sourceUrl, cropRect, frameRange = null) {
  await loadGifLibrary();
  const animation = await decodeGifAnimation(sourceUrl);
  const sourceFrames = Array.isArray(animation.frames) ? animation.frames : [];
  const range = normalizeBrushFrameRange(frameRange, sourceFrames.length) || {
    start: 0,
    end: sourceFrames.length
  };

  const gif = new window.GIF({
    workers: 2,
    quality: 10,
    width: cropRect.width,
    height: cropRect.height,
    background: GIF_TRANSPARENT_MATTE,
    transparent: GIF_TRANSPARENT_MATTE_HEX,
    workerScript: GIF_JS_WORKER_URL
  });

  const frameCanvas = document.createElement("canvas");
  frameCanvas.width = cropRect.width;
  frameCanvas.height = cropRect.height;
  const frameCtx = frameCanvas.getContext("2d", { alpha: true });
  if (!frameCtx) {
    throw new Error("Could not create GIF crop frame.");
  }

  const durations = Array.isArray(animation.durations) ? animation.durations : [];
  for (let index = range.start; index < range.end; index += 1) {
    const sourceFrame = sourceFrames[index];
    if (!sourceFrame) {
      continue;
    }
    frameCtx.save();
    frameCtx.globalCompositeOperation = "copy";
    frameCtx.fillStyle = GIF_TRANSPARENT_MATTE;
    frameCtx.fillRect(0, 0, cropRect.width, cropRect.height);
    frameCtx.globalCompositeOperation = "source-over";
    frameCtx.drawImage(
      sourceFrame,
      cropRect.x,
      cropRect.y,
      cropRect.width,
      cropRect.height,
      0,
      0,
      cropRect.width,
      cropRect.height
    );
    frameCtx.restore();
    const delay = Math.max(
      20,
      Number.isFinite(Number(durations[index])) ? Number(durations[index]) : EXPORT_GIF_FRAME_DELAY_MS
    );
    gif.addFrame(frameCanvas, { copy: true, delay, dispose: 2 });
  }

  const blob = await new Promise((resolve, reject) => {
    gif.on("finished", (finishedBlob) => resolve(finishedBlob));
    gif.on("abort", () => reject(new Error("GIF crop encode aborted.")));
    gif.render();
  });
  return readBlobAsDataUrl(blob);
}

async function applyCropToBrush(brushId, cropRect, options = {}) {
  const brush = findBrushById(brushId);
  if (!brush) {
    return;
  }

  const fullWidth = getBrushOriginalWidth(brush);
  const fullHeight = getBrushOriginalHeight(brush);
  const normalizedRect = normalizeBrushCropRect(cropRect, fullWidth, fullHeight);
  const outputWidth = clamp(Math.round(Number(options.outputWidth) || normalizedRect.width), 1, EXPORT_MAX_DIMENSION);
  const outputHeight = clamp(Math.round(Number(options.outputHeight) || normalizedRect.height), 1, EXPORT_MAX_DIMENSION);
  const nextWeightMode = normalizeBrushWeightMode(options.weightMode || brush.weightMode);

  const sourceUrl = getBrushOriginalUrl(brush);
  if (!sourceUrl) {
    return;
  }

  const isGifBrush =
    isGifUrl(sourceUrl) ||
    /\.gif$/i.test(String(brush.name || ""));
  const frameCount = Math.max(0, Math.floor(Number(options.frameCount) || Number(brush.frameCount) || 0));
  const frameRange = isGifBrush
    ? normalizeBrushFrameRange(options.frameRange || brush.frameRange, frameCount)
    : null;
  const hasPartialFrameRange = isGifBrush && frameRange && !isFullBrushFrameRange(frameRange, frameCount);

  if (isFullBrushCropRect(normalizedRect, fullWidth, fullHeight) && !hasPartialFrameRange) {
    brush.url = sourceUrl;
    brush.width = outputWidth;
    brush.height = outputHeight;
    brush.cropRect = null;
    brush.frameRange = null;
    brush.frameCount = isGifBrush
      ? normalizeBrushFrameCount(frameCount) || normalizeBrushFrameCount(brush.frameCount)
      : 1;
    brush.weightMode = nextWeightMode;
    if (state.brushCursorPreview.brushId === brush.id) {
      resetBrushCursorPreviewSource();
    }
    renderBrushGallery();
    updateBrushStatus();
    updateBrushCursorPreview();
    scheduleSessionSave();
    return;
  }

  const croppedUrl = isGifBrush
    ? await cropAnimatedGifToDataUrl(sourceUrl, normalizedRect, frameRange)
    : await cropStaticImageToDataUrl(sourceUrl, normalizedRect);

  brush.url = croppedUrl;
  brush.width = outputWidth;
  brush.height = outputHeight;
  brush.cropRect = isFullBrushCropRect(normalizedRect, fullWidth, fullHeight) ? null : normalizedRect;
  brush.frameRange = hasPartialFrameRange ? frameRange : null;
  brush.frameCount = hasPartialFrameRange
    ? Math.max(1, frameRange.end - frameRange.start)
    : normalizeBrushFrameCount(brush.frameCount);
  brush.weightMode = nextWeightMode;
  if (state.brushCursorPreview.brushId === brush.id) {
    resetBrushCursorPreviewSource();
  }
  renderBrushGallery();
  updateBrushStatus();
  updateBrushCursorPreview();
  scheduleSessionSave();
}

function openBrushCropPopup(brush) {
  if (!brush) {
    return;
  }

  const fullWidth = getBrushOriginalWidth(brush);
  const fullHeight = getBrushOriginalHeight(brush);
  const currentCrop = getBrushCurrentCropRect(brush);
  const imageUrl = getBrushOriginalUrl(brush);
  if (!imageUrl) {
    return;
  }

  state.brushCropEditor.open = true;
  state.brushCropEditor.brushId = brush.id;
  state.brushCropEditor.imageUrl = imageUrl;
  state.brushCropEditor.imageWidth = fullWidth;
  state.brushCropEditor.imageHeight = fullHeight;
  setBrushCropOutputSize(
    Math.max(1, Number(brush.width) || currentCrop.width),
    Math.max(1, Number(brush.height) || currentCrop.height)
  );
  state.brushCropEditor.frameCount = 0;
  state.brushCropEditor.frameStart = 0;
  state.brushCropEditor.frameEnd = 0;
  state.brushCropEditor.frameDrag = null;
  state.brushCropEditor.frameAnimation = null;
  state.brushCropEditor.frameControlsLoading = false;
  state.brushCropEditor.framePreviewUrls = [];
  state.brushCropEditor.framePreviewIndex = 0;
  clearBrushCropFramePreviewTimer();
  state.brushCropEditor.weightMode = normalizeBrushWeightMode(brush.weightMode);
  state.brushCropEditor.cropRect = currentCrop;
  state.brushCropEditor.drag = null;
  brushCropConfirmButton.disabled = false;
  brushCropCancelButton.disabled = false;
  brushCropModal.classList.add("is-open");
  brushCropModal.setAttribute("aria-hidden", "false");
  delete brushCropImage.dataset.gifPausePending;
  delete brushCropImage.dataset.gifPausedSrc;
  brushCropImage.src = imageUrl;
  applyGifPauseStateToImage(brushCropImage);
  const isGifBrush = getBrushSourceIsGif({ ...brush, url: imageUrl, originalUrl: imageUrl });
  if (isGifBrush) {
    const initialFrameCount =
      normalizeBrushFrameCount(brush.frameCount) ||
      normalizeBrushFrameCount(brush.frameRange?.end) ||
      0;
    const initialRange = normalizeBrushFrameRange(brush.frameRange, initialFrameCount) || {
      start: 0,
      end: initialFrameCount
    };
    state.brushCropEditor.frameCount = initialFrameCount;
    state.brushCropEditor.frameStart = initialRange.start;
    state.brushCropEditor.frameEnd = initialRange.end;
    state.brushCropEditor.frameControlsLoading = !initialFrameCount;
  }
  updateBrushCropResolutionInputs();
  updateBrushCropFrameControls();
  updateBrushCropProbabilityUI();
  void loadBrushCropFrameControls(brush);
  if (brushCropImage.complete && brushCropImage.naturalWidth > 0) {
    renderBrushCropModal();
  }
  setTintPopoverOpen(false);
}

async function loadBrushCropFrameControls(brush) {
  const sourceUrl = getBrushOriginalUrl(brush);
  if (!sourceUrl || !getBrushSourceIsGif({ ...brush, url: sourceUrl, originalUrl: sourceUrl })) {
    return;
  }

  const brushId = Number(brush.id);
  try {
    const animation = await decodeGifAnimation(sourceUrl);
    if (!state.brushCropEditor.open || Number(state.brushCropEditor.brushId) !== brushId) {
      return;
    }
    const frameCount = Math.max(0, Array.isArray(animation.frames) ? animation.frames.length : 0);
    const range = normalizeBrushFrameRange(brush.frameRange, frameCount) || {
      start: 0,
      end: frameCount
    };
    state.brushCropEditor.frameCount = frameCount;
    state.brushCropEditor.frameStart = range.start;
    state.brushCropEditor.frameEnd = range.end;
    state.brushCropEditor.frameAnimation = animation;
    state.brushCropEditor.frameControlsLoading = false;
    state.brushCropEditor.framePreviewUrls = [];
    state.brushCropEditor.framePreviewIndex = range.start;
    const liveBrush = findBrushById(brushId);
    if (liveBrush && frameCount > 0) {
      liveBrush.frameCount = frameCount;
      scheduleSessionSave();
    }
    updateBrushCropFrameControls();
    startBrushCropFramePreview();
  } catch (error) {
    if (state.brushCropEditor.open && Number(state.brushCropEditor.brushId) === brushId) {
      state.brushCropEditor.frameCount = 0;
      state.brushCropEditor.frameAnimation = null;
      state.brushCropEditor.frameControlsLoading = false;
      state.brushCropEditor.framePreviewUrls = [];
      updateBrushCropFrameControls();
    }
  }
}

function closeBrushCropModal() {
  clearBrushCropFramePreviewTimer();
  state.brushCropEditor.open = false;
  state.brushCropEditor.brushId = null;
  state.brushCropEditor.imageUrl = "";
  state.brushCropEditor.imageWidth = 0;
  state.brushCropEditor.imageHeight = 0;
  state.brushCropEditor.outputWidth = 0;
  state.brushCropEditor.outputHeight = 0;
  state.brushCropEditor.frameCount = 0;
  state.brushCropEditor.frameStart = 0;
  state.brushCropEditor.frameEnd = 0;
  state.brushCropEditor.frameDrag = null;
  state.brushCropEditor.frameAnimation = null;
  state.brushCropEditor.frameControlsLoading = false;
  state.brushCropEditor.framePreviewUrls = [];
  state.brushCropEditor.framePreviewIndex = 0;
  state.brushCropEditor.weightMode = "normal";
  state.brushCropEditor.cropRect = null;
  state.brushCropEditor.drag = null;
  brushCropModal.classList.remove("is-open");
  brushCropModal.setAttribute("aria-hidden", "true");
  delete brushCropImage.dataset.gifPausePending;
  delete brushCropImage.dataset.gifPausedSrc;
  brushCropImage.src = "";
}

function setBrushCropRectStyle(element, left, top, width, height) {
  element.style.left = `${left}px`;
  element.style.top = `${top}px`;
  element.style.width = `${Math.max(0, width)}px`;
  element.style.height = `${Math.max(0, height)}px`;
}

function getBrushCropDisplayScale() {
  const fullWidth = Math.max(1, Number(state.brushCropEditor.imageWidth) || 1);
  const fullHeight = Math.max(1, Number(state.brushCropEditor.imageHeight) || 1);
  const imageRect = brushCropImage.getBoundingClientRect();
  return {
    x: imageRect.width / fullWidth,
    y: imageRect.height / fullHeight
  };
}

function renderBrushCropModal() {
  if (!state.brushCropEditor.open || !state.brushCropEditor.cropRect) {
    return;
  }

  const fullWidth = Math.max(1, Number(state.brushCropEditor.imageWidth) || 1);
  const fullHeight = Math.max(1, Number(state.brushCropEditor.imageHeight) || 1);
  state.brushCropEditor.cropRect = normalizeBrushCropRect(
    state.brushCropEditor.cropRect,
    fullWidth,
    fullHeight
  );

  const scale = getBrushCropDisplayScale();
  const imageRect = brushCropImage.getBoundingClientRect();

  const left = state.brushCropEditor.cropRect.x * scale.x;
  const top = state.brushCropEditor.cropRect.y * scale.y;
  const width = state.brushCropEditor.cropRect.width * scale.x;
  const height = state.brushCropEditor.cropRect.height * scale.y;
  const right = left + width;
  const bottom = top + height;

  setBrushCropRectStyle(brushCropSelection, left, top, width, height);
  setBrushCropRectStyle(brushCropShadeTop, 0, 0, imageRect.width, top);
  setBrushCropRectStyle(brushCropShadeBottom, 0, bottom, imageRect.width, imageRect.height - bottom);
  setBrushCropRectStyle(brushCropShadeLeft, 0, top, left, height);
  setBrushCropRectStyle(brushCropShadeRight, right, top, imageRect.width - right, height);
  updateBrushCropResolutionInputs();
  updateBrushCropFrameControls();
}

function beginBrushCropDrag(event, mode, edge = "") {
  if (!state.brushCropEditor.open || !state.brushCropEditor.cropRect) {
    return;
  }

  event.preventDefault();
  state.brushCropEditor.drag = {
    pointerId: event.pointerId,
    mode,
    edge,
    startClientX: event.clientX,
    startClientY: event.clientY,
    startCropRect: { ...state.brushCropEditor.cropRect }
  };
  try {
    brushCropSelection.setPointerCapture(event.pointerId);
  } catch (error) {
    // Best effort pointer capture.
  }
}

function onBrushCropSelectionPointerDown(event) {
  if (!state.brushCropEditor.open || event.button !== 0) {
    return;
  }

  const edgeNode = event.target.closest(".brush-crop-edge");
  if (edgeNode) {
    beginBrushCropDrag(event, "resize", edgeNode.dataset.edge || "");
    return;
  }

  beginBrushCropDrag(event, "move");
}

function onBrushCropPointerMove(event) {
  const drag = state.brushCropEditor.drag;
  if (!state.brushCropEditor.open || !drag || drag.pointerId !== event.pointerId) {
    return;
  }

  event.preventDefault();
  const scale = getBrushCropDisplayScale();
  const safeScaleX = Math.max(scale.x, 0.0001);
  const safeScaleY = Math.max(scale.y, 0.0001);
  const dx = (event.clientX - drag.startClientX) / safeScaleX;
  const dy = (event.clientY - drag.startClientY) / safeScaleY;
  const next = { ...drag.startCropRect };

  if (drag.mode === "move") {
    next.x = drag.startCropRect.x + dx;
    next.y = drag.startCropRect.y + dy;
  } else {
    const edge = String(drag.edge || "");
    if (edge.includes("left")) {
      next.x = drag.startCropRect.x + dx;
      next.width = drag.startCropRect.width - dx;
    }
    if (edge.includes("right")) {
      next.width = drag.startCropRect.width + dx;
    }
    if (edge.includes("top")) {
      next.y = drag.startCropRect.y + dy;
      next.height = drag.startCropRect.height - dy;
    }
    if (edge.includes("bottom")) {
      next.height = drag.startCropRect.height + dy;
    }
  }

  state.brushCropEditor.cropRect = normalizeBrushCropRect(
    next,
    state.brushCropEditor.imageWidth,
    state.brushCropEditor.imageHeight
  );
  syncBrushCropOutputToAspect("width");
  renderBrushCropModal();
}

function onBrushCropPointerUp(event) {
  const drag = state.brushCropEditor.drag;
  if (!drag || drag.pointerId !== event.pointerId) {
    return;
  }

  try {
    if (brushCropSelection.hasPointerCapture(event.pointerId)) {
      brushCropSelection.releasePointerCapture(event.pointerId);
    }
  } catch (error) {
    // Ignore capture release failures.
  }

  state.brushCropEditor.drag = null;
}

async function confirmBrushCropModal() {
  if (!state.brushCropEditor.open || !Number.isFinite(Number(state.brushCropEditor.brushId))) {
    return;
  }

  brushCropConfirmButton.disabled = true;
  brushCropCancelButton.disabled = true;
  try {
    await applyCropToBrush(state.brushCropEditor.brushId, state.brushCropEditor.cropRect || {}, {
      outputWidth: state.brushCropEditor.outputWidth,
      outputHeight: state.brushCropEditor.outputHeight,
      frameCount: state.brushCropEditor.frameCount,
      frameRange: {
        start: state.brushCropEditor.frameStart,
        end: state.brushCropEditor.frameEnd
      },
      weightMode: state.brushCropEditor.weightMode
    });
    closeBrushCropModal();
  } catch (error) {
    brushCropConfirmButton.disabled = false;
    brushCropCancelButton.disabled = false;
  }
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

async function deleteSnapshotFromIndexedDb(tabId) {
  const database = await openSnapshotDb();
  await new Promise((resolve, reject) => {
    const transaction = database.transaction(SESSION_IDB_STORE_NAME, "readwrite");
    transaction.objectStore(SESSION_IDB_STORE_NAME).delete(tabId);
    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error || new Error("Snapshot delete failed"));
    transaction.onabort = () => reject(transaction.error || new Error("Snapshot delete aborted"));
  });
}

async function getSavedCompositionIndex() {
  try {
    const raw = await readSnapshotFromIndexedDb(SAVED_COMPOSITIONS_INDEX_KEY);
    const parsed = raw ? JSON.parse(raw) : [];
    if (!Array.isArray(parsed)) {
      return [];
    }
    return parsed
      .filter((entry) => entry && typeof entry.id === "string")
      .map((entry) => ({
        id: entry.id,
        savedAt: Number(entry.savedAt) || Date.now(),
        stampCount: Math.max(0, Number(entry.stampCount) || 0),
        brushCount: Math.max(0, Number(entry.brushCount) || 0),
        thumbnailUrl: typeof entry.thumbnailUrl === "string" ? entry.thumbnailUrl : "",
        stockCategory:
          typeof entry.stockCategory === "string" && entry.stockCategory.trim()
            ? entry.stockCategory.trim()
            : "custom"
      }))
      .sort((left, right) => Number(right.savedAt) - Number(left.savedAt));
  } catch (error) {
    return [];
  }
}

async function writeSavedCompositionIndex(entries) {
  await writeSnapshotToIndexedDb(SAVED_COMPOSITIONS_INDEX_KEY, JSON.stringify(entries));
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

function getLocalStorageItemSafe(key) {
  try {
    return localStorage.getItem(key);
  } catch (error) {
    return null;
  }
}

function setLocalStorageItemSafe(key, value) {
  try {
    localStorage.setItem(key, value);
    return true;
  } catch (error) {
    return false;
  }
}

function isBlobUrl(url) {
  return typeof url === "string" && url.startsWith("blob:");
}

function normalizeFavoriteBrushSource(source) {
  return typeof source === "string" && source.trim() ? source.trim() : "";
}

function getBrushFavoriteSource(brush) {
  return normalizeFavoriteBrushSource(brush?.originalUrl || brush?.url || "");
}

function loadFavoriteBrushSources() {
  const raw = getLocalStorageItemSafe(FAVORITE_BRUSH_SOURCES_KEY);
  if (!raw) {
    state.favoriteBrushSources = new Set();
    return;
  }

  try {
    const parsed = JSON.parse(raw);
    state.favoriteBrushSources = new Set(
      Array.isArray(parsed)
        ? parsed.map(normalizeFavoriteBrushSource).filter(Boolean)
        : []
    );
  } catch (error) {
    state.favoriteBrushSources = new Set();
  }
}

function saveFavoriteBrushSources() {
  const sources = state.favoriteBrushSources instanceof Set
    ? Array.from(state.favoriteBrushSources).filter(Boolean)
    : [];
  setLocalStorageItemSafe(FAVORITE_BRUSH_SOURCES_KEY, JSON.stringify(sources));
}

function isBrushSourceFavorite(source) {
  const normalized = normalizeFavoriteBrushSource(source);
  return Boolean(normalized && state.favoriteBrushSources instanceof Set && state.favoriteBrushSources.has(normalized));
}

function isBrushFavorite(brush) {
  return isBrushSourceFavorite(getBrushFavoriteSource(brush));
}

function getBrushPresetSource(brush) {
  return normalizeFavoriteBrushSource(brush?.originalUrl || brush?.url || "");
}

function normalizeCustomBrushPresetIndex(index) {
  const numericIndex = Math.floor(Number(index));
  return Number.isFinite(numericIndex) && numericIndex >= 0 && numericIndex < 5
    ? numericIndex
    : null;
}

function getCustomBrushPresetSources(index) {
  const presetIndex = normalizeCustomBrushPresetIndex(index);
  if (presetIndex === null) {
    return new Set();
  }
  if (!Array.isArray(state.customBrushPresetSources)) {
    state.customBrushPresetSources = Array.from({ length: 5 }, () => new Set());
  }
  if (!(state.customBrushPresetSources[presetIndex] instanceof Set)) {
    state.customBrushPresetSources[presetIndex] = new Set();
  }
  return state.customBrushPresetSources[presetIndex];
}

function getCustomBrushPresetSourcesSnapshot() {
  return Array.from({ length: 5 }, (_, index) =>
    Array.from(getCustomBrushPresetSources(index)).filter(Boolean)
  );
}

function normalizeCustomBrushPresetSourcesSnapshot(value) {
  return Array.from({ length: 5 }, (_, index) => {
    const sources = Array.isArray(value?.[index]) ? value[index] : [];
    return new Set(sources.map(normalizeFavoriteBrushSource).filter(Boolean));
  });
}

function loadCustomBrushPresetSources() {
  const raw = getLocalStorageItemSafe(CUSTOM_BRUSH_PRESET_SOURCES_KEY);
  if (!raw) {
    state.customBrushPresetSources = Array.from({ length: 5 }, () => new Set());
    return;
  }

  try {
    state.customBrushPresetSources = normalizeCustomBrushPresetSourcesSnapshot(JSON.parse(raw));
  } catch (error) {
    state.customBrushPresetSources = Array.from({ length: 5 }, () => new Set());
  }
}

function saveCustomBrushPresetSources() {
  setLocalStorageItemSafe(
    CUSTOM_BRUSH_PRESET_SOURCES_KEY,
    JSON.stringify(getCustomBrushPresetSourcesSnapshot())
  );
}

function isActiveCustomBrushPresetSource(source) {
  const presetIndex = normalizeCustomBrushPresetIndex(state.activeCustomBrushPresetIndex);
  if (presetIndex === null) {
    return false;
  }
  const normalized = normalizeFavoriteBrushSource(source);
  return Boolean(normalized && getCustomBrushPresetSources(presetIndex).has(normalized));
}

function clearActiveCustomBrushPreset() {
  state.activeCustomBrushPresetIndex = null;
}

function updateCustomBrushPresetButtons() {
  for (const container of [drawingBrushPresetButtons, brushesBrushPresetButtons]) {
    if (!container) {
      continue;
    }
    container.innerHTML = "";
    const fragment = document.createDocumentFragment();
    for (let index = 0; index < 5; index += 1) {
      const sources = getCustomBrushPresetSources(index);
      const button = document.createElement("button");
      button.type = "button";
      button.className = "custom-brush-preset-button";
      button.dataset.presetIndex = String(index);
      button.textContent = String(index + 1);
      button.title = sources.size
        ? `Load custom brush preset ${index + 1}`
        : `Drop brush images here for preset ${index + 1}`;
      button.setAttribute("aria-label", button.title);
      button.setAttribute("aria-pressed", String(state.activeCustomBrushPresetIndex === index));
      button.disabled = Boolean(state.stockBrushLoadingFolderId);
      button.classList.toggle("has-items", sources.size > 0);
      button.classList.toggle("is-active", state.activeCustomBrushPresetIndex === index);
      button.classList.toggle("is-loading", state.stockBrushLoadingFolderId === `preset-${index}`);
      fragment.appendChild(button);
    }
    container.appendChild(fragment);
  }
}

function updateFavoriteBrushButtons() {
  const count = state.favoriteBrushSources instanceof Set ? state.favoriteBrushSources.size : 0;
  const disabled = Boolean(state.stockBrushLoadingFolderId) || count === 0;
  for (const button of [loadFavoriteBrushesButton, loadFavoriteBrushesFullButton]) {
    if (!button) {
      continue;
    }
    button.disabled = disabled;
    button.classList.toggle("is-active", state.activeStockBrushFolderId === "favorites");
    button.classList.toggle("is-loading", state.stockBrushLoadingFolderId === "favorites");
  }
  updateCustomBrushPresetButtons();
}

function toggleBrushFavorite(brush) {
  const source = getBrushFavoriteSource(brush);
  if (!source) {
    return false;
  }
  if (!(state.favoriteBrushSources instanceof Set)) {
    state.favoriteBrushSources = new Set();
  }
  if (state.favoriteBrushSources.has(source)) {
    state.favoriteBrushSources.delete(source);
  } else {
    state.favoriteBrushSources.add(source);
  }
  saveFavoriteBrushSources();
  updateFavoriteBrushButtons();
  return true;
}

function addBrushToCustomPreset(brush, index) {
  const source = getBrushPresetSource(brush);
  const presetIndex = normalizeCustomBrushPresetIndex(index);
  if (!source || presetIndex === null) {
    return false;
  }
  getCustomBrushPresetSources(presetIndex).add(source);
  saveCustomBrushPresetSources();
  updateCustomBrushPresetButtons();
  return true;
}

function removeBrushFromCustomPreset(brush, index = state.activeCustomBrushPresetIndex) {
  const source = getBrushPresetSource(brush);
  const presetIndex = normalizeCustomBrushPresetIndex(index);
  if (!source || presetIndex === null) {
    return false;
  }
  const sources = getCustomBrushPresetSources(presetIndex);
  const removed = sources.delete(source);
  if (!removed) {
    return false;
  }
  saveCustomBrushPresetSources();
  if (state.activeCustomBrushPresetIndex === presetIndex) {
    const brushIndex = state.brushes.indexOf(brush);
    if (brushIndex >= 0) {
      state.brushes.splice(brushIndex, 1);
      maybeReleaseObjectUrl(brush.url);
    }
    if (state.soloBrushId === brush.id) {
      state.soloBrushId = null;
    }
    if (state.selectedBrushIds instanceof Set) {
      state.selectedBrushIds.delete(brush.id);
    }
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
  }
  updateCustomBrushPresetButtons();
  return true;
}

async function loadCustomBrushPreset(index) {
  const presetIndex = normalizeCustomBrushPresetIndex(index);
  if (presetIndex === null || state.stockBrushLoadingFolderId) {
    return;
  }

  const sources = Array.from(getCustomBrushPresetSources(presetIndex)).filter(Boolean);
  if (!sources.length) {
    updateBrushStatus(`Preset ${presetIndex + 1} is empty.`);
    updateCustomBrushPresetButtons();
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.favoriteReturnState = null;
  state.stockBrushLoadingFolderId = `preset-${presetIndex}`;
  updateCustomBrushPresetButtons();
  updateBrushStatus(`Loading preset ${presetIndex + 1}...`);

  try {
    const loaded = await loadBrushSourceData(sources);
    if (!loaded.length) {
      updateBrushStatus(`Could not load preset ${presetIndex + 1}.`);
      return;
    }

    const previousBrushUrls = state.brushes.map((brush) => brush.url);
    state.brushes = loaded.map((brushData) => {
      const brush = {
        id: state.nextBrushId,
        ...brushData
      };
      state.nextBrushId += 1;
      return brush;
    });
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    state.activeStockBrushFolderId = null;
    state.activeCustomBrushPresetIndex = presetIndex;
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
    for (const oldUrl of previousBrushUrls) {
      maybeReleaseObjectUrl(oldUrl);
    }
    if (state.eraseMode) {
      setEraseMode(false);
    }

    brushInput.value = "";
    updateBrushStatus();
    renderBrushGallery();
    renderStockBrushButtons();
    updateEraseCursorGeometry();
    updateBrushCursorPreview();
    scheduleSessionSave();
  } finally {
    state.stockBrushLoadingFolderId = null;
    renderStockBrushButtons();
  }
}

function cloneBrushForReturnState(brush) {
  return {
    ...brush,
    cropRect: brush?.cropRect ? { ...brush.cropRect } : null,
    frameRange: brush?.frameRange ? { ...brush.frameRange } : null
  };
}

function captureFavoriteReturnState() {
  return {
    brushes: state.brushes.map(cloneBrushForReturnState),
    nextBrushId: state.nextBrushId,
    soloBrushId: state.soloBrushId,
    selectedBrushIds: state.selectedBrushIds instanceof Set
      ? Array.from(state.selectedBrushIds)
      : [],
    activeStockBrushFolderId: state.activeStockBrushFolderId,
    sidebarTab: state.sidebarTab,
    previousSidebarTab: state.previousSidebarTab,
    sidebarCollapsed: state.sidebarCollapsed,
    brushGalleryCollapsed: state.brushGalleryCollapsed,
    brushGallerySort: state.brushGallerySort
  };
}

function restoreFavoriteReturnState() {
  const snapshot = state.favoriteReturnState;
  if (!snapshot) {
    return false;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.brushes = Array.isArray(snapshot.brushes)
    ? snapshot.brushes.map(cloneBrushForReturnState)
    : [];
  clearBrushFrameCountJobs();
  state.nextBrushId = Math.max(1, Number(snapshot.nextBrushId) || 1);
  const brushIds = new Set(state.brushes.map((brush) => brush.id));
  const soloBrushId = Number(snapshot.soloBrushId);
  state.soloBrushId = Number.isFinite(soloBrushId) && brushIds.has(soloBrushId)
    ? soloBrushId
    : null;
  state.selectedBrushIds = new Set(
    Array.isArray(snapshot.selectedBrushIds)
      ? snapshot.selectedBrushIds
          .map((id) => Number(id))
          .filter((id) => Number.isFinite(id) && brushIds.has(id))
      : []
  );
  state.activeStockBrushFolderId =
    typeof snapshot.activeStockBrushFolderId === "string" && snapshot.activeStockBrushFolderId
      ? snapshot.activeStockBrushFolderId
      : null;
  state.sidebarTab = normalizeSidebarTab(snapshot.sidebarTab);
  state.previousSidebarTab = normalizeSidebarTab(snapshot.previousSidebarTab);
  state.sidebarCollapsed = Boolean(snapshot.sidebarCollapsed);
  state.brushGalleryCollapsed = Boolean(snapshot.brushGalleryCollapsed);
  state.brushGallerySort = normalizeBrushGallerySort(snapshot.brushGallerySort);
  state.favoriteReturnState = null;
  state.stockBrushLoadingFolderId = null;
  state.brushCursorPreview.brushId = null;
  resetBrushCursorPreviewSource();

  updateBrushStatus();
  renderBrushGallery();
  renderStockBrushButtons();
  updateSidebarVisibilityUI();
  updateSidebarTabUI();
  updateEraseCursorGeometry();
  updateBrushCursorPreview();
  scheduleSessionSave();
  return true;
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

function getSelectedBrushes() {
  if (!(state.selectedBrushIds instanceof Set) || !state.selectedBrushIds.size) {
    return [];
  }

  const selectedBrushes = [];
  for (const brush of state.brushes) {
    if (state.selectedBrushIds.has(brush.id) && brush.enabled) {
      selectedBrushes.push(brush);
    }
  }

  if (selectedBrushes.length !== state.selectedBrushIds.size) {
    state.selectedBrushIds = new Set(selectedBrushes.map((brush) => brush.id));
  }

  return selectedBrushes;
}

function clearSelectedBrushes() {
  if (state.selectedBrushIds instanceof Set) {
    state.selectedBrushIds.clear();
  } else {
    state.selectedBrushIds = new Set();
  }
}

function setSoloBrushId(brushId) {
  clearSelectedBrushes();
  state.soloBrushId = Number.isFinite(Number(brushId)) ? Number(brushId) : null;
}

function updateSliderText() {
  sizeValue.textContent = String(sizeSlider.value);
  consistentSizeValue.textContent = String(consistentSizeSlider.value);
  spacingValue.textContent = String(getSpacingValue());
  rotationValue.textContent = String(rotationSlider.value);
  opacityValue.textContent = String(opacitySlider.value);
  cursorTrailCountValue.textContent = String(cursorTrailCountSlider.value);
  spraySpreadValue.textContent = String(spraySpreadSlider.value);
  tintAmountValue.textContent = String(tintAmountSlider.value);
}

function mapSpacingSliderToValue(value) {
  const sliderValue = clamp(Math.round(Number(value) || 48), 4, 1200);
  if (sliderValue <= 1000) {
    return sliderValue;
  }
  const progress = (sliderValue - 1000) / 200;
  return Math.round(1000 + progress * 1000);
}

function mapSpacingValueToSlider(value) {
  const spacing = clamp(Math.round(Number(value) || 48), 4, 2000);
  if (spacing <= 1000) {
    return spacing;
  }
  const progress = (spacing - 1000) / 1000;
  return Math.round(1000 + progress * 200);
}

function updateBrushDataToggleUI() {
  const collapsed = Boolean(state.brushGalleryCollapsed);
  brushDataToggleButton.classList.toggle("is-collapsed", collapsed);
  brushDataToggleButton.setAttribute("aria-expanded", String(!collapsed));
  brushDataToggleButton.setAttribute(
    "aria-label",
    collapsed ? "Show brush data gallery" : "Hide brush data gallery"
  );
}

function setBrushGalleryCollapsed(collapsed) {
  state.brushGalleryCollapsed = Boolean(collapsed);
  renderBrushGallery();
  renderStockBrushButtons();
}

function normalizeBrushGallerySort(sortMode) {
  return ["alpha", "area-asc", "area-desc"].includes(sortMode) ? sortMode : "alpha";
}

function setSliderGroupCollapsed(groupId, collapsed) {
  if (!groupId) {
    return;
  }

  const group = document.getElementById(groupId);
  if (!group) {
    return;
  }

  group.classList.toggle("is-slider-collapsed", Boolean(collapsed));
  state.collapsedSliderGroups[groupId] = Boolean(collapsed);

  for (const label of sliderToggleLabels) {
    if (label.dataset.sliderToggleTarget !== groupId) {
      continue;
    }
    label.setAttribute("aria-expanded", String(!collapsed));
  }
}

function getCollapsedSliderGroupSnapshot() {
  const snapshot = {};
  for (const label of sliderToggleLabels) {
    const groupId = label.dataset.sliderToggleTarget;
    if (!groupId) {
      continue;
    }
    const group = document.getElementById(groupId);
    if (!group) {
      continue;
    }
    snapshot[groupId] = group.classList.contains("is-slider-collapsed");
  }
  return snapshot;
}

function applyCollapsedSliderGroupSnapshot(snapshot) {
  state.collapsedSliderGroups = {};
  const source = snapshot && typeof snapshot === "object" ? snapshot : {};
  for (const label of sliderToggleLabels) {
    const groupId = label.dataset.sliderToggleTarget;
    if (!groupId) {
      continue;
    }
    setSliderGroupCollapsed(groupId, Boolean(source[groupId]));
  }
}

function initializeSliderGroupToggles() {
  for (const label of sliderToggleLabels) {
    label.setAttribute("role", "button");
    label.setAttribute("tabindex", "0");
    const groupId = label.dataset.sliderToggleTarget;
    if (!groupId) {
      continue;
    }

    label.addEventListener("click", (event) => {
      event.preventDefault();
      const group = document.getElementById(groupId);
      if (!group) {
        return;
      }
      setSliderGroupCollapsed(groupId, !group.classList.contains("is-slider-collapsed"));
      scheduleSessionSave();
    });

    label.addEventListener("keydown", (event) => {
      if (event.key !== "Enter" && event.key !== " ") {
        return;
      }
      event.preventDefault();
      const group = document.getElementById(groupId);
      if (!group) {
        return;
      }
      setSliderGroupCollapsed(groupId, !group.classList.contains("is-slider-collapsed"));
      scheduleSessionSave();
    });
  }
}

function updateConsistentModeUI() {
  const isConsistentMode = consistentToggle.checked;
  sizeSlider.disabled = isConsistentMode;
  sizeScaleGroup.classList.toggle("is-consistent-size", isConsistentMode);
  if (sizeControlLabel) {
    sizeControlLabel.textContent = isConsistentMode ? "size (consistent)" : "size";
  }
  if (sizeControlLabel) {
    sizeControlLabel.setAttribute("for", isConsistentMode ? "consistentSizeSlider" : "sizeSlider");
  }
  if (sizePercentValueText) {
    sizePercentValueText.hidden = isConsistentMode;
  }
  if (consistentSizeValueText) {
    consistentSizeValueText.hidden = !isConsistentMode;
  }
  if (sizePercentGroup) {
    sizePercentGroup.hidden = isConsistentMode;
  }
  consistentSizeGroup.hidden = !isConsistentMode;
  consistentSizeSlider.disabled = !isConsistentMode;
}

function updateRenderModeUI() {
  renderModeLabel.textContent = renderModeToggle.checked ? "linear" : "point";
  updateBrushCursorPreview();
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

function isShapeDrawMode(mode) {
  return SHAPE_DRAW_MODES.has(mode);
}

function updateDrawModeUI() {
  const isSprayMode = state.drawMode === "spray";
  if (drawModeButtons) {
    const buttons = Array.from(drawModeButtons.querySelectorAll(".draw-mode-button"));
    for (const button of buttons) {
      const isActive = button.dataset.drawMode === state.drawMode;
      button.classList.toggle("is-active", isActive);
      button.setAttribute("aria-pressed", String(isActive));
    }
  }
  spraySpreadGroup.hidden = !isSprayMode;
  spraySpreadSlider.disabled = !isSprayMode;
}

function setDrawMode(nextMode) {
  if (!DRAW_MODES.includes(nextMode)) {
    return;
  }
  if (state.drawMode === nextMode) {
    return;
  }
  cancelShapeDraft();
  if (state.eraseMode) {
    setEraseMode(false);
  }
  state.drawMode = nextMode;
  updateDrawModeUI();
  updateBrushCursorPreview();
  scheduleSessionSave();
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
  trailStamp.loading = "lazy";
  trailStamp.decoding = "async";
  applyGifPauseStateToImage(trailStamp);
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
  const tintSettings = getCurrentTintSettings();
  setElementTintData(trailStamp, tintSettings);
  applyBrushTintStyle(trailStamp, false, tintSettings);
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
  if (
    !cursorTrailToggle.checked ||
    state.exportMode ||
    state.eraseMode ||
    state.panning ||
    !state.pointerInViewport
  ) {
    resetCursorTrailAnchor();
    return;
  }

  if (!state.brushes.length || !hasEnabledBrushes()) {
    resetCursorTrailAnchor();
    return;
  }

  const point = screenToWorld(clientX, clientY);
  const spacing = getSpacingValue();
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

function applyCanvasBackgroundColor(nextColor) {
  const normalized = normalizeHexColor(nextColor, "#ffffff");
  state.canvasBackgroundColor = normalized;
  document.documentElement.style.setProperty("--canvas-bg", normalized);
  if (drawCanvasBgColorInput && drawCanvasBgColorInput.value !== normalized) {
    drawCanvasBgColorInput.value = normalized;
  }
  if (canvasBgColorInput && canvasBgColorInput.value !== normalized) {
    canvasBgColorInput.value = normalized;
  }
  if (exportCanvasBgColorInput && exportCanvasBgColorInput.value !== normalized) {
    exportCanvasBgColorInput.value = normalized;
  }
}

function revokeExportBackgroundImageUrl() {
  if (state.exportBgImageObjectUrl) {
    URL.revokeObjectURL(state.exportBgImageObjectUrl);
  }
  state.exportBgImageObjectUrl = "";
  state.exportBgImagePreviewUrl = "";
}

function normalizeExportBgTileSize(value) {
  return clamp(
    Math.round(Number(value) || 128),
    EXPORT_BG_TILE_MIN_SIZE,
    EXPORT_BG_TILE_MAX_SIZE
  );
}

function mapExportBgTileSliderToSize(value) {
  const sliderValue = clamp(
    Number(value) || 0,
    0,
    EXPORT_BG_TILE_SLIDER_MAX
  );
  if (sliderValue <= EXPORT_BG_TILE_SLIDER_MID) {
    const progress = sliderValue / EXPORT_BG_TILE_SLIDER_MID;
    return normalizeExportBgTileSize(
      EXPORT_BG_TILE_MIN_SIZE +
        (EXPORT_BG_TILE_MID_SIZE - EXPORT_BG_TILE_MIN_SIZE) * progress
    );
  }

  const progress = (sliderValue - EXPORT_BG_TILE_SLIDER_MID) /
    (EXPORT_BG_TILE_SLIDER_MAX - EXPORT_BG_TILE_SLIDER_MID);
  const eased = progress * progress * (3 - 2 * progress);
  return normalizeExportBgTileSize(
    EXPORT_BG_TILE_MID_SIZE +
      (EXPORT_BG_TILE_MAX_SIZE - EXPORT_BG_TILE_MID_SIZE) * eased
  );
}

function mapExportBgTileSizeToSlider(value) {
  const size = normalizeExportBgTileSize(value);
  if (size <= EXPORT_BG_TILE_MID_SIZE) {
    const progress = (size - EXPORT_BG_TILE_MIN_SIZE) /
      (EXPORT_BG_TILE_MID_SIZE - EXPORT_BG_TILE_MIN_SIZE);
    return Math.round(progress * EXPORT_BG_TILE_SLIDER_MID);
  }

  let low = EXPORT_BG_TILE_SLIDER_MID;
  let high = EXPORT_BG_TILE_SLIDER_MAX;
  for (let index = 0; index < 16; index += 1) {
    const middle = (low + high) / 2;
    if (mapExportBgTileSliderToSize(middle) < size) {
      low = middle;
    } else {
      high = middle;
    }
  }
  return Math.round((low + high) / 2);
}

function updateExportBackgroundImageLayer() {
  if (!exportBgImageLayer) {
    return;
  }

  const imageUrl = state.exportBgImagePreviewUrl ||
    (isGifUrl(state.exportBgImageUrl) ? "" : state.exportBgImageUrl) ||
    "";
  const showCheckerboard = state.exportBackgroundEnabled === false;
  const selectionBounds = state.exportSelectionBounds
    ? normalizeExportSelectionBounds(state.exportSelectionBounds)
    : null;
  const shouldShow = Boolean(state.exportMode && selectionBounds && (showCheckerboard || imageUrl));
  exportBgImageLayer.hidden = !shouldShow;
  exportBgImageLayer.classList.toggle("is-checkerboard", showCheckerboard);
  if (!shouldShow) {
    exportBgImageLayer.classList.remove("is-checkerboard");
    exportBgImageLayer.style.removeProperty("background-image");
    return;
  }

  const boundsWidth = Math.max(1, selectionBounds.right - selectionBounds.left);
  const boundsHeight = Math.max(1, selectionBounds.bottom - selectionBounds.top);
  exportBgImageLayer.style.left = `${selectionBounds.left}px`;
  exportBgImageLayer.style.top = `${selectionBounds.top}px`;
  exportBgImageLayer.style.width = `${boundsWidth}px`;
  exportBgImageLayer.style.height = `${boundsHeight}px`;

  if (showCheckerboard) {
    const checkerTileSize = 16 / Math.max(0.0001, Number(state.camera.scale) || 1);
    const checkerOffset = checkerTileSize / 2;
    exportBgImageLayer.style.removeProperty("background-image");
    exportBgImageLayer.style.opacity = "1";
    exportBgImageLayer.style.backgroundPosition = `0 0, ${checkerOffset}px ${checkerOffset}px`;
    exportBgImageLayer.style.backgroundRepeat = "repeat";
    exportBgImageLayer.style.backgroundSize = `${checkerTileSize}px ${checkerTileSize}px`;
    return;
  }

  const opacity = clamp(Number(state.exportBgImageOpacity) || 0, 0, 100);
  exportBgImageLayer.style.backgroundImage = `url("${imageUrl.replace(/"/g, '\\"')}")`;
  exportBgImageLayer.style.opacity = String(opacity / 100);
  exportBgImageLayer.style.backgroundPosition = "center";

  if (state.exportBgImageMode === "tile") {
    const tileWidth = normalizeExportBgTileSize(state.exportBgImageTileSize);
    const naturalWidth = Math.max(1, Number(state.exportBgImageNaturalWidth) || tileWidth);
    const naturalHeight = Math.max(1, Number(state.exportBgImageNaturalHeight) || tileWidth);
    const tileHeight = Math.max(1, Math.round(tileWidth * (naturalHeight / naturalWidth)));
    exportBgImageLayer.style.backgroundRepeat = "repeat";
    exportBgImageLayer.style.backgroundSize = `${tileWidth}px ${tileHeight}px`;
  } else {
    exportBgImageLayer.style.backgroundRepeat = "no-repeat";
    exportBgImageLayer.style.backgroundSize = "cover";
  }
}

function updateExportBackgroundImageUI() {
  const hasImage = Boolean(state.exportBgImageUrl);
  if (clearExportBgImageButton) {
    clearExportBgImageButton.hidden = !hasImage;
    clearExportBgImageButton.disabled = !hasImage;
  }
  if (exportBgImageButton) {
    exportBgImageButton.classList.toggle("has-image", hasImage);
  }
  if (exportBgImagePreview) {
    const previewUrl = state.exportBgImagePreviewUrl ||
      (isGifUrl(state.exportBgImageUrl) ? "" : state.exportBgImageUrl);
    exportBgImagePreview.style.backgroundImage = hasImage && previewUrl ? `url("${previewUrl.replace(/"/g, '\\"')}")` : "";
  }
  if (exportBgImageControls) {
    exportBgImageControls.hidden = !hasImage;
  }
  if (exportBgImageOpacitySlider) {
    exportBgImageOpacitySlider.disabled = !hasImage;
    exportBgImageOpacitySlider.value = String(clamp(Number(state.exportBgImageOpacity) || 0, 0, 100));
  }
  if (exportBgImageOpacityValue) {
    exportBgImageOpacityValue.textContent = String(clamp(Math.round(Number(state.exportBgImageOpacity) || 0), 0, 100));
  }
  if (exportBgImageTileToggle) {
    exportBgImageTileToggle.disabled = !hasImage;
    exportBgImageTileToggle.checked = state.exportBgImageMode === "tile";
  }
  if (exportBgImageModeLabel) {
    exportBgImageModeLabel.textContent = state.exportBgImageMode === "tile" ? "tile" : "stretch";
  }
  if (exportBgImageTileSizeGroup) {
    exportBgImageTileSizeGroup.hidden = !hasImage || state.exportBgImageMode !== "tile";
  }
  if (exportBgImageTileSizeSlider) {
    exportBgImageTileSizeSlider.disabled = !hasImage || state.exportBgImageMode !== "tile";
    exportBgImageTileSizeSlider.value = String(mapExportBgTileSizeToSlider(state.exportBgImageTileSize));
  }
  if (exportBgImageTileSizeValue) {
    exportBgImageTileSizeValue.textContent = String(normalizeExportBgTileSize(state.exportBgImageTileSize));
  }
  updateExportBackgroundImageLayer();
  ensureExportBackgroundStillPreview();
}

function clearExportBackgroundImage() {
  revokeExportBackgroundImageUrl();
  exportBackgroundAnimationCache.clear();
  exportBackgroundStillPreviewCache.clear();
  exportBackgroundRenderCache.clear();
  state.exportBgImageUrl = "";
  state.exportBgImageOpacity = 100;
  state.exportBgImageMode = "stretch";
  state.exportBgImageTileSize = 128;
  state.exportBgImageNaturalWidth = 0;
  state.exportBgImageNaturalHeight = 0;
  updateExportBackgroundImageUI();
  scheduleSessionSave();
}

async function getExportBackgroundStillPreviewUrl(url) {
  if (!isGifUrl(url)) {
    return url;
  }
  if (!exportBackgroundStillPreviewCache.has(url)) {
    exportBackgroundStillPreviewCache.set(
      url,
      decodeGifAnimation(url)
        .then((animation) => {
          const frame = Array.isArray(animation.frames) ? animation.frames[0] : null;
          if (!frame || typeof frame.toDataURL !== "function") {
            return url;
          }
          return frame.toDataURL("image/png");
        })
        .catch(() => url)
    );
  }
  return exportBackgroundStillPreviewCache.get(url);
}

function ensureExportBackgroundStillPreview() {
  const url = state.exportBgImageUrl || "";
  if (!url) {
    state.exportBgImagePreviewUrl = "";
    return;
  }
  if (!isGifUrl(url)) {
    if (state.exportBgImagePreviewUrl !== url) {
      state.exportBgImagePreviewUrl = url;
      updateExportBackgroundImageLayer();
    }
    return;
  }
  getExportBackgroundStillPreviewUrl(url).then((previewUrl) => {
    if (state.exportBgImageUrl !== url || !previewUrl || state.exportBgImagePreviewUrl === previewUrl) {
      return;
    }
    state.exportBgImagePreviewUrl = previewUrl;
    if (exportBgImagePreview) {
      exportBgImagePreview.style.backgroundImage = `url("${previewUrl.replace(/"/g, '\\"')}")`;
    }
    updateExportBackgroundImageLayer();
  });
}

function loadExportBackgroundImageFile(file) {
  if (!file || !(String(file.type || "").startsWith("image/") || ALLOWED_EXTENSIONS.test(file.name || ""))) {
    return;
  }

  readFileAsDataUrl(file)
    .then((dataUrl) => {
      revokeExportBackgroundImageUrl();
      exportBackgroundAnimationCache.clear();
      exportBackgroundStillPreviewCache.clear();
      exportBackgroundRenderCache.clear();
      state.exportBgImageUrl = dataUrl;
      state.exportBgImagePreviewUrl = isGifUrl(dataUrl) ? "" : dataUrl;
      state.exportBgImageNaturalWidth = 0;
      state.exportBgImageNaturalHeight = 0;
      updateExportBackgroundImageUI();

      const probe = new Image();
      probe.onload = () => {
        if (state.exportBgImageUrl !== dataUrl) {
          return;
        }
        state.exportBgImageNaturalWidth = probe.naturalWidth || 0;
        state.exportBgImageNaturalHeight = probe.naturalHeight || 0;
        updateExportBackgroundImageUI();
        scheduleSessionSave();
      };
      probe.src = dataUrl;
      scheduleSessionSave();
    })
    .catch(() => {
      updateBrushStatus("Could not load background image.");
    });
}

function updateSettingsPanelUI() {
  if (drawCanvasBgRow) {
    drawCanvasBgRow.hidden = !state.showDrawBackgroundColorControl;
  }
  if (drawCanvasBgColorInput) {
    drawCanvasBgColorInput.value = normalizeHexColor(state.canvasBackgroundColor, "#ffffff");
  }
  if (canvasBgColorInput) {
    canvasBgColorInput.value = normalizeHexColor(state.canvasBackgroundColor, "#ffffff");
  }
  if (exportCanvasBgColorInput) {
    exportCanvasBgColorInput.value = normalizeHexColor(state.canvasBackgroundColor, "#ffffff");
  }
  if (exportCanvasBgRow) {
    exportCanvasBgRow.hidden = state.exportBackgroundEnabled === false;
  }
  if (exportBackgroundToggle) {
    exportBackgroundToggle.checked = Boolean(state.exportBackgroundEnabled);
  }
  if (exportSeeBeyondToggle) {
    exportSeeBeyondToggle.checked = state.exportSeeBeyondEnabled !== false;
  }
  updateExportBackgroundImageUI();
  updateExportAnimationUI();
  if (gifCountToggle) {
    gifCountToggle.checked = Boolean(state.showGifCountIndicator);
  }
  if (gifPauseToggle) {
    gifPauseToggle.checked = state.showGifPauseButton !== false;
  }
  if (drawBkgColorToggle) {
    drawBkgColorToggle.checked = Boolean(state.showDrawBackgroundColorControl);
  }
  if (brushPreviewToggle) {
    brushPreviewToggle.checked = state.brushPreviewEnabled !== false;
  }
}

function isGifStampElement(element) {
  if (!(element instanceof HTMLImageElement)) {
    return false;
  }

  const brushId = Number(element.dataset.brushId);
  const brush = Number.isFinite(brushId) ? findBrushById(brushId) : null;
  const brushName = brush ? String(brush.name || "") : "";
  const sourceUrl =
    element.dataset.brushUrl ||
    element.dataset.gifPausedSrc ||
    element.currentSrc ||
    element.getAttribute("src") ||
    (brush ? String(brush.url || "") : "");

  return isGifUrl(sourceUrl) || /\.gif$/i.test(brushName);
}

function getPlacedGifCount() {
  let gifCount = 0;
  for (const element of getVisibleStampElements()) {
    if (isGifStampElement(element)) {
      gifCount += 1;
    }
  }
  return gifCount;
}

function updateGifCountIndicator() {
  if (!gifCountIndicator) {
    return;
  }

  const shouldShow = Boolean(state.showGifCountIndicator);
  gifCountIndicator.hidden = !shouldShow;
  if (!shouldShow) {
    updateGifPauseButtonPosition();
    return;
  }

  const gifCount = getPlacedGifCount();
  gifCountIndicator.textContent = `${gifCount.toLocaleString()} ${gifCount === 1 ? "gif" : "gifs"}`;
  updateGifPauseButtonPosition();
}

function normalizeSidebarTab(tab) {
  if (tab === "main") {
    return "draw";
  }
  return SIDEBAR_TABS.includes(tab) ? tab : "draw";
}

function isDrawingModeActive() {
  return state.sidebarTab === "draw" || state.sidebarTab === "brushes";
}

function isLeftDragPanModeActive() {
  return ["edit", "settings"].includes(state.sidebarTab);
}

function setSidebarTab(tab, options = {}) {
  if (state.exportTask) {
    return;
  }

  const nextTab = normalizeSidebarTab(tab);
  if (state.sidebarTab === nextTab) {
    if (state.sidebarCollapsed) {
      state.sidebarCollapsed = false;
      updateSidebarVisibilityUI();
      scheduleSessionSave();
    }
    updateSidebarTabUI();
    return;
  }

  if (nextTab !== "export" && state.exportMode && !options.keepExportMode) {
    exitExportMode();
  }

  if (nextTab === "settings") {
    state.previousSidebarTab = state.sidebarTab === "settings" ? "draw" : state.sidebarTab;
  } else if (state.sidebarTab !== "settings") {
    state.previousSidebarTab = nextTab;
  }

  state.sidebarTab = nextTab;
  if (nextTab !== "draw" && nextTab !== "brushes") {
    cancelShapeDraft();
    clearCursorTrail();
  }
  updateSidebarTabUI();
  renderBrushGallery();
  updateEraseCursorVisibility();
  updateBrushCursorPreview();
  scheduleSessionSave();
}

function updateBrushDataControlPlacement(activeTab) {
  if (!brushDataControlGroup || !drawingBrushDataSlot || !brushDataPanel) {
    return;
  }

  const target = activeTab === "brushes" ? brushDataPanel : drawingBrushDataSlot;
  if (brushDataControlGroup.parentElement !== target) {
    target.appendChild(brushDataControlGroup);
  }
}

function updateSidebarTabUI() {
  const activeTab = normalizeSidebarTab(state.sidebarTab);
  state.sidebarTab = activeTab;
  controlsPanel.dataset.sidebarMode = activeTab;
  viewport.classList.toggle("is-editing-layers", activeTab === "edit");
  updateBrushDataControlPlacement(activeTab);

  for (const panel of sidebarPanels) {
    panel.hidden = panel.dataset.sidebarPanel !== activeTab;
  }

  if (controlsMain && !controlsMain.dataset.sidebarPanel) {
    controlsMain.hidden = activeTab !== "draw";
  }

  if (sidebarOptionsButton) {
    const isSettingsTab = activeTab === "settings";
    sidebarOptionsButton.classList.toggle("is-active", isSettingsTab);
    sidebarOptionsButton.setAttribute("aria-pressed", String(isSettingsTab));
    sidebarOptionsButton.setAttribute(
      "aria-label",
      isSettingsTab ? "Show drawing controls" : "Show settings"
    );
  }

  for (const button of mainModeTabButtons) {
    const buttonTab = normalizeSidebarTab(button.dataset.sidebarTab);
    const isActive = buttonTab === activeTab;
    button.classList.toggle("is-active", isActive);
    button.setAttribute("aria-pressed", String(isActive));
  }

  if (activeTab !== "draw") {
    setTintPopoverOpen(false);
  }
  if (activeTab === "community" && !state.savedCompositionsLoaded) {
    void loadSavedCompositions();
  }
  renderEditLayers();
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

function normalizeRotationDegrees(angle) {
  let normalized = Number(angle);
  if (!Number.isFinite(normalized)) {
    return 0;
  }
  while (normalized > 180) {
    normalized -= 360;
  }
  while (normalized <= -180) {
    normalized += 360;
  }
  return normalized;
}

function getRotationFromIndicatorPointer(clientX, clientY) {
  const rect = rotationIndicator.getBoundingClientRect();
  const centerX = rect.left + rect.width / 2;
  const centerY = rect.top + rect.height / 2;
  const dx = clientX - centerX;
  const dy = clientY - centerY;
  if (Math.hypot(dx, dy) < 2) {
    return null;
  }
  const angle = (Math.atan2(dy, dx) * 180) / Math.PI + 90;
  return normalizeRotationDegrees(angle);
}

function applyRotationFromIndicatorPointer(clientX, clientY) {
  const angle = getRotationFromIndicatorPointer(clientX, clientY);
  if (angle === null) {
    return false;
  }
  setInputNumericValue(rotationSlider, angle);
  updateSliderText();
  updateRotationIndicator();
  updateActiveStrokeTailRotation();
  updateBrushCursorPreview();
  scheduleSessionSave();
  return true;
}

function stopRotationIndicatorDrag(pointerId = null) {
  const drag = state.rotationIndicatorDrag;
  if (!drag) {
    return;
  }
  if (pointerId !== null && drag.pointerId !== pointerId) {
    return;
  }

  try {
    if (rotationIndicator.hasPointerCapture(drag.pointerId)) {
      rotationIndicator.releasePointerCapture(drag.pointerId);
    }
  } catch (error) {
    // Ignore release failures for ended pointers.
  }

  state.rotationIndicatorDrag = null;
  rotationIndicator.classList.remove("is-dragging");
}

function onRotationIndicatorPointerDown(event) {
  if (event.button !== 0 && event.pointerType !== "touch") {
    return;
  }

  event.preventDefault();
  state.rotationIndicatorDrag = { pointerId: event.pointerId };
  rotationIndicator.classList.add("is-dragging");
  try {
    rotationIndicator.setPointerCapture(event.pointerId);
  } catch (error) {
    // Continue even if capture is unavailable.
  }
  applyRotationFromIndicatorPointer(event.clientX, event.clientY);
}

function onRotationIndicatorPointerMove(event) {
  if (!state.rotationIndicatorDrag || state.rotationIndicatorDrag.pointerId !== event.pointerId) {
    return;
  }
  event.preventDefault();
  applyRotationFromIndicatorPointer(event.clientX, event.clientY);
}

function worldToScreen(worldX, worldY) {
  return {
    x: worldX * state.camera.scale + state.camera.x,
    y: worldY * state.camera.scale + state.camera.y
  };
}

function getVisibleStampElements() {
  return Array.from(world.getElementsByClassName("stamp")).filter(
    (element) => !element.classList.contains("is-layer-hidden")
  );
}

function getViewportWorldBounds(marginPx = STAMP_VIEWPORT_CULL_MARGIN_PX) {
  const rect = viewport.getBoundingClientRect();
  const scale = Math.max(0.0001, state.camera.scale);
  return {
    left: (-marginPx - state.camera.x) / scale,
    top: (-marginPx - state.camera.y) / scale,
    right: (rect.width + marginPx - state.camera.x) / scale,
    bottom: (rect.height + marginPx - state.camera.y) / scale
  };
}

function getCachedStampWorldBounds(element) {
  const left = Number(element.dataset.worldLeft);
  const top = Number(element.dataset.worldTop);
  const right = Number(element.dataset.worldRight);
  const bottom = Number(element.dataset.worldBottom);
  if (
    Number.isFinite(left) &&
    Number.isFinite(top) &&
    Number.isFinite(right) &&
    Number.isFinite(bottom)
  ) {
    return { left, top, right, bottom };
  }
  return getStampWorldBounds(element);
}

function setStampViewportRendered(stamp, rendered) {
  if (!(stamp instanceof HTMLImageElement)) {
    return;
  }

  if (rendered) {
    if (isViewportCulledStamp(stamp)) {
      delete stamp.dataset.viewportCulled;
      stamp.classList.remove("is-culled");
      const source = stamp.dataset.brushUrl || stamp.dataset.gifPausedSrc || "";
      if (source && stamp.getAttribute("src") !== source) {
        stamp.src = source;
      }
      applyGifPauseStateToImage(stamp);
    }
    return;
  }

  if (state.gifAnimationsPaused || isViewportCulledStamp(stamp)) {
    return;
  }

  stamp.dataset.viewportCulled = "true";
  stamp.classList.add("is-culled");
  stamp.src = TRANSPARENT_STAMP_SRC;
}

function updateStampViewportVisibility(stamp, viewportBounds = getViewportWorldBounds()) {
  if (!(stamp instanceof HTMLImageElement) || !stamp.classList.contains("stamp")) {
    return;
  }

  const bounds = getCachedStampWorldBounds(stamp);
  setStampViewportRendered(stamp, rectsIntersect(bounds, viewportBounds));
}

function refreshStampViewportVisibility() {
  const viewportBounds = getViewportWorldBounds();
  const stamps = world.getElementsByClassName("stamp");
  for (let index = 0; index < stamps.length; index += 1) {
    updateStampViewportVisibility(stamps[index], viewportBounds);
  }
}

function scheduleStampVisibilityRefresh() {
  if (state.stampVisibilityRafId !== null) {
    return;
  }
  state.stampVisibilityRafId = window.requestAnimationFrame(() => {
    state.stampVisibilityRafId = null;
    refreshStampViewportVisibility();
  });
}

function restoreAllCulledStampSources() {
  if (state.stampVisibilityRafId !== null) {
    window.cancelAnimationFrame(state.stampVisibilityRafId);
    state.stampVisibilityRafId = null;
  }
  const stamps = world.getElementsByClassName("stamp");
  for (let index = 0; index < stamps.length; index += 1) {
    setStampViewportRendered(stamps[index], true);
  }
}

function getStampWorldBoundsFromLayout(left, top, width, height, rotationDegrees) {
  const centerX = left + width / 2;
  const centerY = top + height / 2;
  const radians = (rotationDegrees * Math.PI) / 180;
  const absCos = Math.abs(Math.cos(radians));
  const absSin = Math.abs(Math.sin(radians));
  const halfWidth = width / 2;
  const halfHeight = height / 2;
  const extentX = halfWidth * absCos + halfHeight * absSin;
  const extentY = halfWidth * absSin + halfHeight * absCos;
  return {
    left: centerX - extentX,
    top: centerY - extentY,
    right: centerX + extentX,
    bottom: centerY + extentY
  };
}

function getStampWorldBounds(element) {
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  const rotation = Number(element.dataset.rotation) || 0;
  return getStampWorldBoundsFromLayout(left, top, width, height, rotation);
}

function getStampIndexCellCoord(value) {
  return Math.floor(value / STAMP_INDEX_CELL_SIZE);
}

function getStampIndexCellKey(cellX, cellY) {
  return `${cellX}:${cellY}`;
}

function unregisterStampSpatialCells(element) {
  const keys = state.stampSpatialCells.get(element);
  if (!Array.isArray(keys) || !keys.length) {
    return;
  }

  for (const key of keys) {
    const bucket = state.stampSpatialBuckets.get(key);
    if (!bucket) {
      continue;
    }
    bucket.delete(element);
    if (!bucket.size) {
      state.stampSpatialBuckets.delete(key);
    }
  }

  state.stampSpatialCells.delete(element);
}

function cacheStampWorldBounds(element) {
  if (!element || !element.classList || !element.classList.contains("stamp")) {
    return null;
  }

  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  if (width <= 0 || height <= 0) {
    return null;
  }
  const rotation = Number(element.dataset.rotation) || 0;
  const bounds = getStampWorldBoundsFromLayout(left, top, width, height, rotation);
  element.dataset.worldLeft = String(bounds.left);
  element.dataset.worldTop = String(bounds.top);
  element.dataset.worldRight = String(bounds.right);
  element.dataset.worldBottom = String(bounds.bottom);
  return bounds;
}

function registerStampSpatialCells(element) {
  if (!element || !element.classList || !element.classList.contains("stamp")) {
    return;
  }

  unregisterStampSpatialCells(element);
  const bounds = cacheStampWorldBounds(element);
  if (!bounds) {
    return;
  }

  const minCellX = getStampIndexCellCoord(bounds.left);
  const maxCellX = getStampIndexCellCoord(bounds.right);
  const minCellY = getStampIndexCellCoord(bounds.top);
  const maxCellY = getStampIndexCellCoord(bounds.bottom);
  const occupiedKeys = [];

  for (let cellX = minCellX; cellX <= maxCellX; cellX += 1) {
    for (let cellY = minCellY; cellY <= maxCellY; cellY += 1) {
      const key = getStampIndexCellKey(cellX, cellY);
      let bucket = state.stampSpatialBuckets.get(key);
      if (!bucket) {
        bucket = new Set();
        state.stampSpatialBuckets.set(key, bucket);
      }
      bucket.add(element);
      occupiedKeys.push(key);
    }
  }

  if (occupiedKeys.length) {
    state.stampSpatialCells.set(element, occupiedKeys);
  }
}

function clearStampSpatialIndex() {
  state.stampSpatialBuckets.clear();
  state.stampSpatialCells = new WeakMap();
}

function rebuildStampSpatialIndexFromDom() {
  clearStampSpatialIndex();
  const elements = world.getElementsByClassName("stamp");
  for (let index = 0; index < elements.length; index += 1) {
    const element = elements[index];
    if (element.classList.contains("is-layer-hidden")) {
      continue;
    }
    registerStampSpatialCells(element);
  }
}

function getEraseCandidateStamps(centerX, centerY, radius) {
  if (!state.stampSpatialBuckets.size && getVisibleStampCount() > 0) {
    rebuildStampSpatialIndexFromDom();
  }

  const minCellX = getStampIndexCellCoord(centerX - radius);
  const maxCellX = getStampIndexCellCoord(centerX + radius);
  const minCellY = getStampIndexCellCoord(centerY - radius);
  const maxCellY = getStampIndexCellCoord(centerY + radius);
  const candidates = new Set();

  for (let cellX = minCellX; cellX <= maxCellX; cellX += 1) {
    for (let cellY = minCellY; cellY <= maxCellY; cellY += 1) {
      const bucket = state.stampSpatialBuckets.get(getStampIndexCellKey(cellX, cellY));
      if (!bucket) {
        continue;
      }
      for (const element of bucket) {
        if (element.parentElement === world && !element.classList.contains("is-layer-hidden")) {
          candidates.add(element);
        }
      }
    }
  }

  return candidates;
}

function normalizeExportSelectionBounds(bounds) {
  const fallback = { left: -150, top: -100, right: 150, bottom: 100 };
  if (!bounds) {
    return fallback;
  }

  let left = Number(bounds.left);
  let top = Number(bounds.top);
  let right = Number(bounds.right);
  let bottom = Number(bounds.bottom);

  if (![left, top, right, bottom].every((value) => Number.isFinite(value))) {
    return fallback;
  }

  if (left > right) {
    [left, right] = [right, left];
  }
  if (top > bottom) {
    [top, bottom] = [bottom, top];
  }

  if (right - left < EXPORT_MIN_SIZE) {
    const centerX = (left + right) / 2;
    left = centerX - EXPORT_MIN_SIZE / 2;
    right = centerX + EXPORT_MIN_SIZE / 2;
  }
  if (bottom - top < EXPORT_MIN_SIZE) {
    const centerY = (top + bottom) / 2;
    top = centerY - EXPORT_MIN_SIZE / 2;
    bottom = centerY + EXPORT_MIN_SIZE / 2;
  }

  return { left, top, right, bottom };
}

function getDefaultExportSelectionBounds() {
  const rect = viewport.getBoundingClientRect();
  const center = screenToWorld(rect.left + rect.width / 2, rect.top + rect.height / 2);
  const halfWidth = Math.max(160, (rect.width / state.camera.scale) * 0.3);
  const halfHeight = Math.max(120, (rect.height / state.camera.scale) * 0.3);
  return {
    left: center.x - halfWidth,
    right: center.x + halfWidth,
    top: center.y - halfHeight,
    bottom: center.y + halfHeight
  };
}

function computeInitialExportSelectionBounds() {
  const stamps = getVisibleStampElements();
  if (!stamps.length) {
    return normalizeExportSelectionBounds(getDefaultExportSelectionBounds());
  }

  let minX = Number.POSITIVE_INFINITY;
  let minY = Number.POSITIVE_INFINITY;
  let maxX = Number.NEGATIVE_INFINITY;
  let maxY = Number.NEGATIVE_INFINITY;

  for (const element of stamps) {
    const bounds = getStampWorldBounds(element);
    minX = Math.min(minX, bounds.left);
    minY = Math.min(minY, bounds.top);
    maxX = Math.max(maxX, bounds.right);
    maxY = Math.max(maxY, bounds.bottom);
  }

  return normalizeExportSelectionBounds({
    left: minX - EXPORT_SELECTION_PADDING,
    top: minY - EXPORT_SELECTION_PADDING,
    right: maxX + EXPORT_SELECTION_PADDING,
    bottom: maxY + EXPORT_SELECTION_PADDING
  });
}

function setFixedRectStyle(element, left, top, width, height) {
  element.style.left = `${left}px`;
  element.style.top = `${top}px`;
  element.style.width = `${Math.max(0, width)}px`;
  element.style.height = `${Math.max(0, height)}px`;
}

function getExportBaseResolution(bounds) {
  const normalized = normalizeExportSelectionBounds(bounds);
  return {
    width: Math.max(1, normalized.right - normalized.left),
    height: Math.max(1, normalized.bottom - normalized.top)
  };
}

function getExportMinScaleMultiplier(bounds) {
  const base = getExportBaseResolution(bounds);
  return EXPORT_MIN_DIMENSION / Math.max(base.width, base.height);
}

function getExportMaxScaleMultiplier(bounds) {
  const base = getExportBaseResolution(bounds);
  return Math.max(
    getExportMinScaleMultiplier(bounds),
    Math.min(EXPORT_MAX_DIMENSION / base.width, EXPORT_MAX_DIMENSION / base.height)
  );
}

function getExportScaleMultiplier(bounds = null) {
  const rawMultiplier = Number(state.exportScalePercent) / 100;
  if (!bounds) {
    return Number.isFinite(rawMultiplier) ? rawMultiplier : 1;
  }
  return clamp(
    Number.isFinite(rawMultiplier) ? rawMultiplier : 1,
    getExportMinScaleMultiplier(bounds),
    getExportMaxScaleMultiplier(bounds)
  );
}

function getExportScaledResolution(bounds) {
  const normalized = normalizeExportSelectionBounds(bounds);
  const multiplier = getExportScaleMultiplier(normalized);
  const width = Math.max(1, Math.round((normalized.right - normalized.left) * multiplier));
  const height = Math.max(1, Math.round((normalized.bottom - normalized.top) * multiplier));
  return { width, height };
}

function getSavedExportScalePercent() {
  const scalePercent = Number(state.exportScalePercent);
  return Number.isFinite(scalePercent) && scalePercent > 0 ? scalePercent : 100;
}

function rememberCurrentExportSetup() {
  if (!state.exportMode || !state.exportSelectionBounds) {
    return;
  }

  state.lastExportSetup = {
    selectionBounds: { ...normalizeExportSelectionBounds(state.exportSelectionBounds) },
    scalePercent: getSavedExportScalePercent()
  };
  scheduleSessionSave();
}

function clearRememberedExportSetup() {
  state.lastExportSetup = null;
}

function getRememberedExportSetup() {
  if (!state.lastExportSetup || !state.lastExportSetup.selectionBounds) {
    return null;
  }

  const selectionBounds = normalizeExportSelectionBounds(state.lastExportSetup.selectionBounds);
  const scalePercent = Number(state.lastExportSetup.scalePercent);
  return {
    selectionBounds,
    scalePercent: Number.isFinite(scalePercent) && scalePercent > 0 ? scalePercent : 100
  };
}

function normalizeExportSetupSnapshot(setup) {
  if (!setup || !setup.selectionBounds) {
    return null;
  }
  const selectionBounds = normalizeExportSelectionBounds(setup.selectionBounds);
  const scalePercent = Number(setup.scalePercent);
  return {
    selectionBounds,
    scalePercent: Number.isFinite(scalePercent) && scalePercent > 0 ? scalePercent : 100
  };
}

function rectContainsRect(outer, inner) {
  const epsilon = 0.001;
  return (
    inner.left >= outer.left - epsilon &&
    inner.right <= outer.right + epsilon &&
    inner.top >= outer.top - epsilon &&
    inner.bottom <= outer.bottom + epsilon
  );
}

function updateRememberedExportSetupForAddedStroke(stroke) {
  const remembered = getRememberedExportSetup();
  if (!remembered || !stroke || !Array.isArray(stroke.elements)) {
    return;
  }

  for (const element of stroke.elements) {
    if (element.parentElement !== world) {
      continue;
    }
    if (!rectContainsRect(remembered.selectionBounds, getStampWorldBounds(element))) {
      clearRememberedExportSetup();
      return;
    }
  }
}

function updateExportResolutionInputs(resolution) {
  const width = String(clamp(Math.round(resolution.width), 1, EXPORT_MAX_DIMENSION));
  const height = String(clamp(Math.round(resolution.height), 1, EXPORT_MAX_DIMENSION));
  exportWidthInput.value = width;
  exportHeightInput.value = height;
  if (exportSidebarWidthInput) {
    exportSidebarWidthInput.value = width;
  }
  if (exportSidebarHeightInput) {
    exportSidebarHeightInput.value = height;
  }
}

function updateExportScaleButtonsUI() {
  const currentScalePercent = Number(state.exportScalePercent);
  const safeScalePercent = Number.isFinite(currentScalePercent) && currentScalePercent > 0
    ? currentScalePercent
    : 100;
  const normalized = state.exportSelectionBounds
    ? normalizeExportSelectionBounds(state.exportSelectionBounds)
    : null;
  const maxScalePercent = normalized ? getExportMaxScaleMultiplier(normalized) * 100 : Number.POSITIVE_INFINITY;
  const nearestScale = EXPORT_SCALE_PRESETS.reduce((nearest, preset) => {
    const nearestDistance = Math.abs(nearest - safeScalePercent);
    const presetDistance = Math.abs(preset - safeScalePercent);
    return presetDistance < nearestDistance ? preset : nearest;
  }, EXPORT_SCALE_PRESETS[0]);
  const hasExactPreset = EXPORT_SCALE_PRESETS.some(
    (preset) => Math.abs(preset - safeScalePercent) < 0.0001
  );
  const customScaleLabel = `${Math.round(safeScalePercent)}%`;

  for (const button of [...exportScaleButtons, ...exportSidebarScaleButtons]) {
    const scale = Number(button.dataset.scale);
    const isActive = Math.abs(scale - nearestScale) < 0.0001;
    const displayedScale = isActive && !hasExactPreset ? safeScalePercent : scale;
    const isOverLimit = displayedScale > maxScalePercent + 0.0001;
    button.textContent = isActive && !hasExactPreset ? customScaleLabel : `${scale}%`;
    button.classList.toggle("is-active", isActive);
    button.classList.toggle("is-over-limit", isOverLimit);
    button.setAttribute("aria-pressed", isActive ? "true" : "false");
    button.setAttribute(
      "aria-label",
      isOverLimit
        ? `${button.textContent} export scale exceeds 10000px limit`
        : `${button.textContent} export scale`
    );
    button.disabled = Boolean(state.exportTask);
  }
}

function getExportFrameCountOverride() {
  const value = String(state.exportAnimationFrameCount || "").trim();
  if (!value) {
    return null;
  }
  const numericValue = Math.floor(Number(value));
  if (!Number.isFinite(numericValue)) {
    return null;
  }
  return clamp(numericValue, 1, EXPORT_MAX_FRAME_COUNT);
}

function updateExportAnimationUI() {
  const isAuto = state.exportAnimationAuto !== false;
  const hasFrameCountOverride = Boolean(String(state.exportAnimationFrameCount || "").trim());
  if (exportAnimationDurationLabel) {
    exportAnimationDurationLabel.textContent = isAuto ? "gif duration: auto" : "gif duration: manual";
  }
  if (exportAnimationAutoToggle) {
    exportAnimationAutoToggle.checked = isAuto;
    exportAnimationAutoToggle.disabled = Boolean(state.exportTask);
  }
  if (exportAnimationManualControls) {
    exportAnimationManualControls.hidden = isAuto;
  }
  for (const button of exportAnimationSecondsButtons) {
    const seconds = Number(button.dataset.seconds);
    const isActive =
      !hasFrameCountOverride &&
      Math.abs(seconds - Number(state.exportAnimationSeconds)) < 0.0001;
    button.classList.toggle("is-active", isActive);
    button.setAttribute("aria-pressed", String(isActive));
    button.disabled = isAuto || Boolean(state.exportTask);
  }
  if (exportFrameCountInput) {
    exportFrameCountInput.value = state.exportAnimationFrameCount || "";
    exportFrameCountInput.disabled = isAuto || Boolean(state.exportTask);
  }

  const videoAuto = state.exportVideoAuto !== false;
  if (exportVideoDurationLabel) {
    exportVideoDurationLabel.textContent = videoAuto ? "video duration: auto" : "video duration: manual";
  }
  if (exportVideoAutoToggle) {
    exportVideoAutoToggle.checked = videoAuto;
    exportVideoAutoToggle.disabled = Boolean(state.exportTask);
  }
  if (exportVideoLengthRow) {
    exportVideoLengthRow.hidden = videoAuto;
  }
  if (exportVideoLengthInput) {
    exportVideoLengthInput.value = String(state.exportVideoSeconds ?? 3);
    exportVideoLengthInput.disabled = videoAuto || Boolean(state.exportTask);
  }
}

function setExportScalePercent(nextScalePercent) {
  const numericScale = Number(nextScalePercent);
  if (!Number.isFinite(numericScale) || !EXPORT_SCALE_PRESETS.includes(numericScale)) {
    return;
  }
  state.exportScalePercent = numericScale;
  updateExportScaleButtonsUI();
  updateExportOverlayGeometry();
}

function setExportResolutionFromInput(axis, rawValue) {
  if (!state.exportMode || !state.exportSelectionBounds) {
    return;
  }

  const requested = Number(rawValue);
  if (!Number.isFinite(requested)) {
    updateExportOverlayGeometry();
    return;
  }

  const normalized = normalizeExportSelectionBounds(state.exportSelectionBounds);
  const base = getExportBaseResolution(normalized);
  const sourceDimension = axis === "height" ? base.height : base.width;
  const targetDimension = clamp(Math.round(requested), EXPORT_MIN_DIMENSION, EXPORT_MAX_DIMENSION);
  const requestedMultiplier = targetDimension / sourceDimension;
  const nextMultiplier = clamp(
    requestedMultiplier,
    getExportMinScaleMultiplier(normalized),
    getExportMaxScaleMultiplier(normalized)
  );

  state.exportScalePercent = nextMultiplier * 100;
  updateExportScaleButtonsUI();
  updateExportOverlayGeometry();
}

function hasGifStampOnCanvas() {
  for (const element of getVisibleStampElements()) {
    if (isGifStampElement(element)) {
      return true;
    }
  }
  return false;
}

function updateExportOverlayGeometry() {
  if (!state.exportMode || !state.exportSelectionBounds) {
    return;
  }

  const normalized = normalizeExportSelectionBounds(state.exportSelectionBounds);
  state.exportSelectionBounds = normalized;
  exportOverlay.classList.toggle("is-see-beyond-off", state.exportSeeBeyondEnabled === false);

  const topLeft = worldToScreen(normalized.left, normalized.top);
  const bottomRight = worldToScreen(normalized.right, normalized.bottom);
  const selectionLeft = Math.min(topLeft.x, bottomRight.x);
  const selectionTop = Math.min(topLeft.y, bottomRight.y);
  const selectionRight = Math.max(topLeft.x, bottomRight.x);
  const selectionBottom = Math.max(topLeft.y, bottomRight.y);
  const selectionWidth = Math.max(1, selectionRight - selectionLeft);
  const selectionHeight = Math.max(1, selectionBottom - selectionTop);

  setFixedRectStyle(exportSelection, selectionLeft, selectionTop, selectionWidth, selectionHeight);
  updateExportBackgroundImageLayer();

  const viewportRect = viewport.getBoundingClientRect();
  const viewportLeft = viewportRect.left;
  const viewportTop = viewportRect.top;
  const viewportRight = viewportRect.right;
  const viewportBottom = viewportRect.bottom;
  const viewportWidth = viewportRect.width;
  const viewportHeight = viewportRect.height;

  const clipLeft = clamp(selectionLeft, viewportLeft, viewportRight);
  const clipTop = clamp(selectionTop, viewportTop, viewportBottom);
  const clipRight = clamp(selectionRight, viewportLeft, viewportRight);
  const clipBottom = clamp(selectionBottom, viewportTop, viewportBottom);
  const clipWidth = Math.max(0, clipRight - clipLeft);
  const clipHeight = Math.max(0, clipBottom - clipTop);

  setFixedRectStyle(exportShadeTop, viewportLeft, viewportTop, viewportWidth, clipTop - viewportTop);
  setFixedRectStyle(
    exportShadeBottom,
    viewportLeft,
    clipBottom,
    viewportWidth,
    viewportBottom - clipBottom
  );
  setFixedRectStyle(exportShadeLeft, viewportLeft, clipTop, clipLeft - viewportLeft, clipHeight);
  setFixedRectStyle(exportShadeRight, clipRight, clipTop, viewportRight - clipRight, clipHeight);

  const centerX = selectionLeft + selectionWidth / 2;
  exportMeta.style.left = `${centerX}px`;
  exportMeta.style.top = `${selectionBottom + 8}px`;
  exportMeta.style.transform = "translateX(-50%)";

  const scaledResolution = getExportScaledResolution(normalized);
  updateExportResolutionInputs(scaledResolution);
  updateExportScaleButtonsUI();
  rememberCurrentExportSetup();
}

function updateExportModeUI() {
  const isOpen = Boolean(state.exportMode && state.exportSelectionBounds);
  exportOverlay.hidden = !isOpen;
  exportOverlay.setAttribute("aria-hidden", String(!isOpen));
  if (!state.exportTask) {
    resetExportProgress(exportButton, "Render GIF");
    resetExportProgress(exportVideoButton, "Render Video");
    exportButton.setAttribute("aria-label", "Render GIF");
    exportButton.title = "Render GIF";
    if (exportVideoButton) {
      exportVideoButton.setAttribute("aria-label", "Render Video");
      exportVideoButton.title = "Render Video";
    }
  } else {
    const activeButton = state.exportTask.button || exportButton;
    if (!activeButton.style.getPropertyValue("--export-progress")) {
      updateExportProgress(
        state.exportTask,
        state.exportTask.progress || 0,
        state.exportTask.progressLabel || (state.exportTask.cancelled ? "Cancelling export" : "Exporting")
      );
    }
  }
  exportModeButton.setAttribute("aria-pressed", String(isOpen || state.sidebarTab === "export"));
  exportModeButton.classList.toggle("is-active", isOpen || state.sidebarTab === "export");
  exportActions.classList.toggle("is-active", isOpen);
  exportButton.disabled = !isOpen || Boolean(state.exportTask);
  exportButton.classList.toggle("is-loading", Boolean(state.exportTask && state.exportTask.button === exportButton));
  exportCancelButton.disabled = !state.exportTask;
  if (exportVideoButton) {
    exportVideoButton.disabled = !isOpen || Boolean(state.exportTask);
    exportVideoButton.classList.toggle("is-loading", Boolean(state.exportTask && state.exportTask.button === exportVideoButton));
  }
  if (exportVideoCancelButton) {
    exportVideoCancelButton.disabled = !state.exportTask;
  }
  exportModeButton.disabled = Boolean(state.exportTask) || getVisibleStampCount() === 0;
  exportWidthInput.disabled = Boolean(state.exportTask);
  exportHeightInput.disabled = Boolean(state.exportTask);
  if (exportSidebarWidthInput) {
    exportSidebarWidthInput.disabled = Boolean(state.exportTask);
  }
  if (exportSidebarHeightInput) {
    exportSidebarHeightInput.disabled = Boolean(state.exportTask);
  }
  updateExportScaleButtonsUI();
  updateExportAnimationUI();
  if (isOpen) {
    updateExportOverlayGeometry();
  } else {
    updateExportBackgroundImageLayer();
  }
  updateEraseCursorVisibility();
  updateBrushCursorPreview();
}

function exitExportMode(options = {}) {
  rememberCurrentExportSetup();
  state.exportMode = false;
  state.exportSelectionBounds = null;
  state.exportDrag = null;
  state.exportScalePercent = 100;
  updateExportModeUI();
  updateUndoState();
  if (options.focusButton) {
    exportModeButton.focus();
  }
}

function enterExportMode() {
  if (state.placementTask || state.exportTask) {
    return;
  }

  if (!getVisibleStampCount()) {
    return;
  }

  if (clearConfirmModal.classList.contains("is-open")) {
    closeClearConfirmModal();
  }

  if (state.drawing) {
    stopDrawing(state.drawing.pointerId);
  }
  if (state.erasing) {
    stopErasing(state.erasing.pointerId);
  }
  if (state.shapeDraft) {
    cancelShapeDraft();
  }
  if (state.panning) {
    stopPanning(state.panning.pointerId);
  }
  if (state.touchGesture) {
    endTouchGesture();
  }

  const remembered = getRememberedExportSetup();
  state.exportMode = true;
  state.exportSelectionBounds = remembered
    ? remembered.selectionBounds
    : computeInitialExportSelectionBounds();
  state.exportScalePercent = remembered ? remembered.scalePercent : 100;
  state.exportDrag = null;
  updateExportModeUI();
  updateUndoState();
}

function startExportSelectionDrag(pointerId, options) {
  if (!state.exportMode || !state.exportSelectionBounds) {
    return;
  }

  const mode = options?.mode === "move" ? "move" : "resize";
  const edge = typeof options?.edge === "string" ? options.edge : null;
  const clientX = Number(options?.clientX);
  const clientY = Number(options?.clientY);
  const pointerPoint =
    Number.isFinite(clientX) && Number.isFinite(clientY)
      ? screenToWorld(clientX, clientY)
      : { x: 0, y: 0 };

  state.exportDrag = {
    pointerId,
    mode,
    edge,
    startWorldX: pointerPoint.x,
    startWorldY: pointerPoint.y,
    originBounds: { ...state.exportSelectionBounds }
  };
  try {
    exportSelection.setPointerCapture(pointerId);
  } catch (error) {
    // Continue without capture if pointer ended before capture.
  }
}

function getAspectLockedExportResizeBounds(origin, edge, point, symmetric = false) {
  const normalized = normalizeExportSelectionBounds(origin);
  const width = Math.max(EXPORT_MIN_SIZE, normalized.right - normalized.left);
  const height = Math.max(EXPORT_MIN_SIZE, normalized.bottom - normalized.top);
  const aspect = width / height;
  const centerX = (normalized.left + normalized.right) / 2;
  const centerY = (normalized.top + normalized.bottom) / 2;
  const hasLeft = edge.includes("left");
  const hasRight = edge.includes("right");
  const hasTop = edge.includes("top");
  const hasBottom = edge.includes("bottom");
  const horizontal = hasLeft || hasRight;
  const vertical = hasTop || hasBottom;

  if (symmetric) {
    let halfWidth = width / 2;
    let halfHeight = height / 2;
    if (horizontal) {
      halfWidth = Math.max(EXPORT_MIN_SIZE / 2, Math.abs(point.x - centerX));
    }
    if (vertical) {
      halfHeight = Math.max(EXPORT_MIN_SIZE / 2, Math.abs(point.y - centerY));
    }
    if (horizontal && vertical) {
      const scale = Math.max(halfWidth / (width / 2), halfHeight / (height / 2));
      halfWidth = Math.max(EXPORT_MIN_SIZE / 2, (width / 2) * scale);
      halfHeight = Math.max(EXPORT_MIN_SIZE / 2, halfWidth / aspect);
    } else if (horizontal) {
      halfHeight = Math.max(EXPORT_MIN_SIZE / 2, halfWidth / aspect);
    } else if (vertical) {
      halfWidth = Math.max(EXPORT_MIN_SIZE / 2, halfHeight * aspect);
    }
    return {
      left: centerX - halfWidth,
      right: centerX + halfWidth,
      top: centerY - halfHeight,
      bottom: centerY + halfHeight
    };
  }

  const next = { ...normalized };
  if (horizontal && vertical) {
    const anchorX = hasLeft ? normalized.right : normalized.left;
    const anchorY = hasTop ? normalized.bottom : normalized.top;
    let nextWidth = Math.max(EXPORT_MIN_SIZE, Math.abs(point.x - anchorX));
    let nextHeight = Math.max(EXPORT_MIN_SIZE, Math.abs(point.y - anchorY));
    if (nextWidth / nextHeight > aspect) {
      nextWidth = nextHeight * aspect;
    } else {
      nextHeight = nextWidth / aspect;
    }
    next.left = hasLeft ? anchorX - nextWidth : anchorX;
    next.right = hasRight ? anchorX + nextWidth : anchorX;
    next.top = hasTop ? anchorY - nextHeight : anchorY;
    next.bottom = hasBottom ? anchorY + nextHeight : anchorY;
    return next;
  }

  if (horizontal) {
    const anchorX = hasLeft ? normalized.right : normalized.left;
    const nextWidth = Math.max(EXPORT_MIN_SIZE, Math.abs(point.x - anchorX));
    const nextHeight = Math.max(EXPORT_MIN_SIZE, nextWidth / aspect);
    next.left = hasLeft ? anchorX - nextWidth : anchorX;
    next.right = hasRight ? anchorX + nextWidth : anchorX;
    next.top = centerY - nextHeight / 2;
    next.bottom = centerY + nextHeight / 2;
    return next;
  }

  if (vertical) {
    const anchorY = hasTop ? normalized.bottom : normalized.top;
    const nextHeight = Math.max(EXPORT_MIN_SIZE, Math.abs(point.y - anchorY));
    const nextWidth = Math.max(EXPORT_MIN_SIZE, nextHeight * aspect);
    next.top = hasTop ? anchorY - nextHeight : anchorY;
    next.bottom = hasBottom ? anchorY + nextHeight : anchorY;
    next.left = centerX - nextWidth / 2;
    next.right = centerX + nextWidth / 2;
  }
  return next;
}

function getSymmetricExportResizeBounds(origin, edge, point) {
  const normalized = normalizeExportSelectionBounds(origin);
  const centerX = (normalized.left + normalized.right) / 2;
  const centerY = (normalized.top + normalized.bottom) / 2;
  const hasHorizontal = edge.includes("left") || edge.includes("right");
  const hasVertical = edge.includes("top") || edge.includes("bottom");
  const halfWidth = hasHorizontal
    ? Math.max(EXPORT_MIN_SIZE / 2, Math.abs(point.x - centerX))
    : Math.max(EXPORT_MIN_SIZE / 2, (normalized.right - normalized.left) / 2);
  const halfHeight = hasVertical
    ? Math.max(EXPORT_MIN_SIZE / 2, Math.abs(point.y - centerY))
    : Math.max(EXPORT_MIN_SIZE / 2, (normalized.bottom - normalized.top) / 2);
  return {
    left: centerX - halfWidth,
    right: centerX + halfWidth,
    top: centerY - halfHeight,
    bottom: centerY + halfHeight
  };
}

function getFreeExportResizeBounds(origin, edge, point) {
  const next = { ...normalizeExportSelectionBounds(origin) };
  if (edge.includes("left")) {
    next.left = Math.min(point.x, next.right - EXPORT_MIN_SIZE);
  }
  if (edge.includes("right")) {
    next.right = Math.max(point.x, next.left + EXPORT_MIN_SIZE);
  }
  if (edge.includes("top")) {
    next.top = Math.min(point.y, next.bottom - EXPORT_MIN_SIZE);
  }
  if (edge.includes("bottom")) {
    next.bottom = Math.max(point.y, next.top + EXPORT_MIN_SIZE);
  }
  return next;
}

function updateExportSelectionDrag(pointerId, clientX, clientY, modifiers = {}) {
  if (!state.exportDrag || state.exportDrag.pointerId !== pointerId || !state.exportSelectionBounds) {
    return;
  }

  const point = screenToWorld(clientX, clientY);
  const origin = state.exportDrag.originBounds || state.exportSelectionBounds;
  const next = { ...origin };

  if (state.exportDrag.mode === "move") {
    const deltaX = point.x - state.exportDrag.startWorldX;
    const deltaY = point.y - state.exportDrag.startWorldY;
    next.left += deltaX;
    next.right += deltaX;
    next.top += deltaY;
    next.bottom += deltaY;
  } else {
    const edge = String(state.exportDrag.edge || "");
    const lockAspect = Boolean(modifiers.shiftKey);
    const resizeFromCenter = Boolean(modifiers.altKey);
    Object.assign(
      next,
      lockAspect
        ? getAspectLockedExportResizeBounds(origin, edge, point, resizeFromCenter)
        : resizeFromCenter
        ? getSymmetricExportResizeBounds(origin, edge, point)
        : getFreeExportResizeBounds(origin, edge, point)
    );
  }

  state.exportSelectionBounds = normalizeExportSelectionBounds(next);
  updateExportOverlayGeometry();
}

function stopExportSelectionDrag(pointerId) {
  if (!state.exportDrag || state.exportDrag.pointerId !== pointerId) {
    return;
  }
  try {
    if (exportSelection.hasPointerCapture(pointerId)) {
      exportSelection.releasePointerCapture(pointerId);
    }
  } catch (error) {
    // Ignore release errors for already-finished pointers.
  }
  state.exportDrag = null;
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
  state.eraseCursorRadiusScreen = diameterScreen / 2;
  scheduleEraseCursorRender();
}

function renderEraseCursorPositionNow() {
  const radius = Number.isFinite(state.eraseCursorRadiusScreen) ? state.eraseCursorRadiusScreen : 9;
  const x = state.lastPointerClientX - radius;
  const y = state.lastPointerClientY - radius;
  eraseCursor.style.transform = `translate3d(${x}px, ${y}px, 0)`;
}

function scheduleEraseCursorRender() {
  if (state.eraseCursorRafId !== null) {
    return;
  }
  state.eraseCursorRafId = window.requestAnimationFrame(() => {
    state.eraseCursorRafId = null;
    renderEraseCursorPositionNow();
  });
}

function updateEraseCursorPosition(clientX, clientY) {
  state.lastPointerClientX = clientX;
  state.lastPointerClientY = clientY;
  scheduleEraseCursorRender();
}

function updateEraseCursorVisibility() {
  const shouldShow =
    state.eraseMode &&
    isDrawingModeActive() &&
    state.pointerInViewport &&
    !state.panning &&
    !state.touchGesture &&
    !state.exportMode;
  eraseCursor.classList.toggle("is-visible", shouldShow);
}

function updateEraseModeUI() {
  eraseModeButton.classList.toggle("is-active", state.eraseMode);
  eraseModeButton.setAttribute("aria-pressed", String(state.eraseMode));
  viewport.classList.toggle("is-erasing", state.eraseMode);
  updateEraseCursorGeometry();
  updateEraseCursorVisibility();
}

function clearShortcutPreviewHideTimer() {
  if (state.shortcutPreview.hideTimerId !== null) {
    window.clearTimeout(state.shortcutPreview.hideTimerId);
    state.shortcutPreview.hideTimerId = null;
  }
}

function hideShortcutPreview(resetBrush = false) {
  clearShortcutPreviewHideTimer();
  shortcutPreview.classList.remove("is-visible");
  if (resetBrush) {
    state.shortcutPreview.brushId = null;
  }
}

function scheduleShortcutPreviewHide() {
  clearShortcutPreviewHideTimer();
  state.shortcutPreview.hideTimerId = window.setTimeout(() => {
    hideShortcutPreview();
  }, 520);
}

function getShortcutPreviewBrush() {
  const remembered = findBrushById(Number(state.shortcutPreview.brushId));
  if (remembered) {
    return remembered;
  }

  const soloBrush = getSoloBrush();
  if (soloBrush) {
    state.shortcutPreview.brushId = soloBrush.id;
    return soloBrush;
  }

  const selectedBrushes = getSelectedBrushes();
  if (selectedBrushes.length) {
    const rememberedSelected = selectedBrushes.find(
      (brush) => brush.id === Number(state.shortcutPreview.brushId)
    );
    const selectedBrush = rememberedSelected || selectedBrushes[0];
    state.shortcutPreview.brushId = selectedBrush.id;
    return selectedBrush;
  }

  const enabledBrush = state.brushes.find((brush) => brush.enabled);
  if (enabledBrush) {
    state.shortcutPreview.brushId = enabledBrush.id;
    return enabledBrush;
  }

  const fallbackBrush = state.brushes[0] || null;
  if (fallbackBrush) {
    state.shortcutPreview.brushId = fallbackBrush.id;
  }
  return fallbackBrush;
}

function getBrushPlacementSize(brush) {
  if (!brush) {
    return { width: 0, height: 0 };
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
  return { width, height };
}

function showShortcutPreviewAt(clientX, clientY) {
  const brush = getShortcutPreviewBrush();
  if (!brush) {
    hideShortcutPreview(true);
    return;
  }

  const worldSize = getBrushPlacementSize(brush);
  let displayWidth = Math.max(8, worldSize.width * state.camera.scale);
  let displayHeight = Math.max(8, worldSize.height * state.camera.scale);
  const maxDisplaySize = 220;
  if (displayWidth > maxDisplaySize || displayHeight > maxDisplaySize) {
    const scaleDown = Math.min(maxDisplaySize / displayWidth, maxDisplaySize / displayHeight);
    displayWidth *= scaleDown;
    displayHeight *= scaleDown;
  }

  const left = clientX - displayWidth / 2;
  const top = clientY - displayHeight / 2;

  const rotation = parseNumericInputValue(rotationSlider, 0);
  const opacity = clamp(Number(opacitySlider.value) / 100, 0, 1);

  delete shortcutPreview.dataset.gifPausePending;
  delete shortcutPreview.dataset.gifPausedSrc;
  shortcutPreview.src = brush.url;
  applyGifPauseStateToImage(shortcutPreview);
  shortcutPreview.style.left = `${left}px`;
  shortcutPreview.style.top = `${top}px`;
  shortcutPreview.style.width = `${displayWidth}px`;
  shortcutPreview.style.height = `${displayHeight}px`;
  shortcutPreview.style.transform = `rotate(${rotation}deg)`;
  shortcutPreview.style.opacity = String(opacity);
  shortcutPreview.style.imageRendering = renderModeToggle.checked ? "auto" : "pixelated";
  applyBrushTintStyle(shortcutPreview, false, getCurrentTintSettings());
  shortcutPreview.classList.add("is-visible");
  scheduleShortcutPreviewHide();
}

function resetBrushCursorPreviewSource() {
  state.brushCursorPreview.sourceUrl = "";
  state.brushCursorPreview.frozenUrl = "";
  state.brushCursorPreview.loadingUrl = "";
  state.brushCursorPreview.failedUrl = "";
  state.brushCursorPreview.renderedUrl = "";
  state.brushCursorPreview.loadToken += 1;
  if (brushCursorPreview) {
    brushCursorPreview.removeAttribute("src");
  }
}

function hideBrushCursorPreview(resetBrush = false) {
  if (!brushCursorPreview) {
    return;
  }
  brushCursorPreview.classList.remove("is-visible");
  if (resetBrush) {
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
  }
}

function isGifBrush(brush) {
  if (!brush) {
    return false;
  }
  return isGifUrl(brush.url) || /\.gif$/i.test(String(brush.name || ""));
}

function getBrushCursorPreviewBrush() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    state.brushCursorPreview.brushId = soloBrush.id;
    return soloBrush;
  }

  const selectedBrushes = getSelectedBrushes();
  if (selectedBrushes.length) {
    const rememberedSelected = selectedBrushes.find(
      (brush) => brush.id === Number(state.brushCursorPreview.brushId)
    );
    const selectedBrush = rememberedSelected || selectedBrushes[0];
    state.brushCursorPreview.brushId = selectedBrush.id;
    return selectedBrush;
  }

  const remembered = findBrushById(Number(state.brushCursorPreview.brushId));
  if (remembered && remembered.enabled) {
    return remembered;
  }

  const enabledBrush = state.brushes.find((brush) => brush.enabled) || null;
  if (enabledBrush) {
    state.brushCursorPreview.brushId = enabledBrush.id;
  }
  return enabledBrush;
}

function requestFrozenBrushCursorPreviewSource(sourceUrl) {
  const previewState = state.brushCursorPreview;

  if (previewState.sourceUrl !== sourceUrl) {
    previewState.sourceUrl = sourceUrl;
    previewState.frozenUrl = "";
    previewState.loadingUrl = "";
    previewState.failedUrl = "";
    previewState.loadToken += 1;
  }

  if (previewState.frozenUrl) {
    return previewState.frozenUrl;
  }

  if (previewState.loadingUrl === sourceUrl || previewState.failedUrl === sourceUrl) {
    return "";
  }

  const token = previewState.loadToken + 1;
  previewState.loadToken = token;
  previewState.loadingUrl = sourceUrl;

  const loader = new Image();
  loader.onload = () => {
    if (
      state.brushCursorPreview.loadToken !== token ||
      state.brushCursorPreview.sourceUrl !== sourceUrl
    ) {
      return;
    }

    let frozenUrl = "";
    try {
      frozenUrl = captureImageStillFrame(loader);
    } catch (error) {
      frozenUrl = "";
    }
    state.brushCursorPreview.loadingUrl = "";
    if (frozenUrl) {
      state.brushCursorPreview.frozenUrl = frozenUrl;
      updateBrushCursorPreview();
    } else {
      state.brushCursorPreview.failedUrl = sourceUrl;
      hideBrushCursorPreview();
    }
  };
  loader.onerror = () => {
    if (
      state.brushCursorPreview.loadToken !== token ||
      state.brushCursorPreview.sourceUrl !== sourceUrl
    ) {
      return;
    }
    state.brushCursorPreview.loadingUrl = "";
    state.brushCursorPreview.failedUrl = sourceUrl;
    hideBrushCursorPreview();
  };
  loader.src = sourceUrl;

  return "";
}

function getBrushCursorPreviewSource(brush) {
  if (!brush || typeof brush.url !== "string" || !brush.url) {
    return "";
  }

  if (isGifBrush(brush)) {
    return requestFrozenBrushCursorPreviewSource(brush.url);
  }

  if (state.brushCursorPreview.sourceUrl !== brush.url) {
    state.brushCursorPreview.sourceUrl = brush.url;
    state.brushCursorPreview.frozenUrl = "";
    state.brushCursorPreview.loadingUrl = "";
    state.brushCursorPreview.failedUrl = "";
    state.brushCursorPreview.loadToken += 1;
  }
  return brush.url;
}

function shouldShowBrushCursorPreview() {
  return Boolean(
    brushCursorPreview &&
      state.brushPreviewEnabled !== false &&
      isDrawingModeActive() &&
      state.pointerInViewport &&
      !state.eraseMode &&
      !state.panning &&
      !state.touchGesture &&
      !state.exportMode &&
      !state.exportTask &&
      !state.placementTask &&
      !state.drawing &&
      !state.erasing &&
      !state.shapeDraft
  );
}

function updateBrushCursorPreview() {
  if (!shouldShowBrushCursorPreview()) {
    hideBrushCursorPreview();
    return;
  }

  const brush = getBrushCursorPreviewBrush();
  if (!brush) {
    hideBrushCursorPreview(true);
    return;
  }

  const sourceUrl = getBrushCursorPreviewSource(brush);
  if (!sourceUrl) {
    hideBrushCursorPreview();
    return;
  }

  const worldSize = getBrushPlacementSize(brush);
  const displayWidth = Math.max(1, worldSize.width * state.camera.scale);
  const displayHeight = Math.max(1, worldSize.height * state.camera.scale);
  const left = state.lastPointerClientX - displayWidth / 2;
  const top = state.lastPointerClientY - displayHeight / 2;
  const rotation = parseNumericInputValue(rotationSlider, 0);

  if (state.brushCursorPreview.renderedUrl !== sourceUrl) {
    brushCursorPreview.src = sourceUrl;
    state.brushCursorPreview.renderedUrl = sourceUrl;
  }
  brushCursorPreview.style.left = `${left}px`;
  brushCursorPreview.style.top = `${top}px`;
  brushCursorPreview.style.width = `${displayWidth}px`;
  brushCursorPreview.style.height = `${displayHeight}px`;
  brushCursorPreview.style.transform = `rotate(${rotation}deg)`;
  brushCursorPreview.style.opacity = "0.2";
  brushCursorPreview.style.imageRendering = renderModeToggle.checked ? "auto" : "pixelated";
  applyBrushTintStyle(brushCursorPreview, false, getCurrentTintSettings());
  brushCursorPreview.classList.add("is-visible");
}

function updatePanningStateClass() {
  viewport.classList.toggle("is-panning", Boolean(state.panning || state.touchGesture));
  updateBrushCursorPreview();
}

function cancelDrawingForGesture() {
  if (!state.drawing) {
    return;
  }

  const drawing = state.drawing;
  for (const element of drawing.stroke.elements) {
    decrementUrlRef(element.dataset.brushUrl);
    element.remove();
  }
  if (viewport.hasPointerCapture(drawing.pointerId)) {
    viewport.releasePointerCapture(drawing.pointerId);
  }
  state.drawing = null;
  viewport.classList.remove("is-drawing");
}

function cancelErasingForGesture() {
  if (!state.erasing) {
    return;
  }

  const erasing = state.erasing;
  if (viewport.hasPointerCapture(erasing.pointerId)) {
    viewport.releasePointerCapture(erasing.pointerId);
  }

  if (erasing.changed && erasing.removalContext.records.length) {
    undoEraseAction({ removals: erasing.removalContext.records });
  }

  state.erasing = null;
}

function hideShapePreview() {
  shapePreview.className = "";
  shapePreview.style.width = "0";
  shapePreview.style.height = "0";
  shapePreview.style.transform = "none";
}

function cancelShapeDraft() {
  if (
    state.shapeDraft &&
    state.shapeDraft.pointerId !== null &&
    viewport.hasPointerCapture(state.shapeDraft.pointerId)
  ) {
    viewport.releasePointerCapture(state.shapeDraft.pointerId);
  }
  state.shapeDraft = null;
  viewport.classList.remove("is-drawing");
  hideShapePreview();
  updateBrushCursorPreview();
}

function cancelShapeDraftForGesture() {
  if (!state.shapeDraft) {
    return;
  }
  cancelShapeDraft();
}

function startTouchGestureFromActiveTouches() {
  const touchEntries = Array.from(state.touchPointers.entries());
  if (touchEntries.length < 2) {
    return false;
  }

  if (state.drawing) {
    cancelDrawingForGesture();
  }
  if (state.erasing) {
    cancelErasingForGesture();
  }
  if (state.shapeDraft) {
    cancelShapeDraftForGesture();
  }
  if (state.panning) {
    stopPanning(state.panning.pointerId);
  }

  resetCursorTrailAnchor();
  const [[pointerIdA, pointA], [pointerIdB, pointB]] = touchEntries;
  const midX = (pointA.x + pointB.x) / 2;
  const midY = (pointA.y + pointB.y) / 2;
  const startDistance = Math.max(8, Math.hypot(pointB.x - pointA.x, pointB.y - pointA.y));
  const midWorld = screenToWorld(midX, midY);

  state.touchGesture = {
    pointerIdA,
    pointerIdB,
    startDistance,
    startScale: state.camera.scale,
    startWorldX: midWorld.x,
    startWorldY: midWorld.y
  };

  for (const pointerId of [pointerIdA, pointerIdB]) {
    if (!viewport.hasPointerCapture(pointerId)) {
      try {
        viewport.setPointerCapture(pointerId);
      } catch (error) {
        // Best effort capture for smoother multitouch tracking.
      }
    }
  }

  updatePanningStateClass();
  updateEraseCursorVisibility();
  return true;
}

function updateTouchGestureFromActiveTouches() {
  if (!state.touchGesture) {
    return;
  }

  const pointA = state.touchPointers.get(state.touchGesture.pointerIdA);
  const pointB = state.touchPointers.get(state.touchGesture.pointerIdB);
  if (!pointA || !pointB) {
    return;
  }

  const midX = (pointA.x + pointB.x) / 2;
  const midY = (pointA.y + pointB.y) / 2;
  const distance = Math.max(8, Math.hypot(pointB.x - pointA.x, pointB.y - pointA.y));
  const scaleFactor = distance / state.touchGesture.startDistance;
  const nextScale = clamp(state.touchGesture.startScale * scaleFactor, MIN_CAMERA_SCALE, MAX_CAMERA_SCALE);

  state.camera.x = midX - state.touchGesture.startWorldX * nextScale;
  state.camera.y = midY - state.touchGesture.startWorldY * nextScale;
  state.camera.scale = nextScale;
  renderCamera();
  updateEraseCursorGeometry();
}

function endTouchGesture() {
  if (!state.touchGesture) {
    return;
  }

  for (const pointerId of [state.touchGesture.pointerIdA, state.touchGesture.pointerIdB]) {
    if (viewport.hasPointerCapture(pointerId)) {
      try {
        viewport.releasePointerCapture(pointerId);
      } catch (error) {
        // Ignore capture release errors from already-ended pointers.
      }
    }
  }

  state.touchGesture = null;
  updatePanningStateClass();
  resetCursorTrailAnchor();
  updateEraseCursorVisibility();
  scheduleSessionSave();
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
  const deltaCenterX = centerStampX - centerX;
  const deltaCenterY = centerStampY - centerY;
  const centerDistanceSq = deltaCenterX * deltaCenterX + deltaCenterY * deltaCenterY;
  const centerDistance = Math.sqrt(centerDistanceSq);

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
  const gridSize = ERASER_SAMPLE_GRID_SIZE;
  const totalSamples = gridSize * gridSize;
  const threshold = Math.ceil(totalSamples * 0.5);
  const radiusSq = radius * radius;
  let insideSamples = 0;
  const isAxisAligned = Math.abs(rotation % 360) < 0.0001;

  for (let row = 0; row < gridSize; row += 1) {
    const localY = ((row + 0.5) / gridSize - 0.5) * height;
    for (let col = 0; col < gridSize; col += 1) {
      const localX = ((col + 0.5) / gridSize - 0.5) * width;
      const sampleX = isAxisAligned
        ? centerStampX + localX
        : centerStampX + localX * cos - localY * sin;
      const sampleY = isAxisAligned
        ? centerStampY + localY
        : centerStampY + localX * sin + localY * cos;
      const sampleDeltaX = sampleX - centerX;
      const sampleDeltaY = sampleY - centerY;
      if (sampleDeltaX * sampleDeltaX + sampleDeltaY * sampleDeltaY <= radiusSq) {
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
    unregisterStampSpatialCells(element);
    decrementUrlRef(element.dataset.brushUrl);
    element.remove();
    state.stampCount = Math.max(0, state.stampCount - 1);
  }
}

function eraseAtPoint(worldX, worldY, radiusWorld, removalContext = null) {
  let removedAny = false;
  const candidates = getEraseCandidateStamps(worldX, worldY, radiusWorld);
  for (const element of candidates) {
    if (element.parentElement !== world) {
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

  const step = Math.max(ERASER_PATH_MIN_STEP, radiusWorld * ERASER_PATH_STEP_FACTOR);
  const stepX = dx / distance;
  const stepY = dy / distance;
  const originX = erasing.lastX;
  const originY = erasing.lastY;
  let traveled = 0;
  let processed = 0;
  let latestSampleX = originX;
  let latestSampleY = originY;

  while (traveled + step <= distance && processed < ERASER_MAX_SAMPLES_PER_FRAME) {
    traveled += step;
    const sampleX = originX + stepX * traveled;
    const sampleY = originY + stepY * traveled;
    if (eraseAtPoint(sampleX, sampleY, radiusWorld, erasing.removalContext)) {
      erasing.changed = true;
    }
    latestSampleX = sampleX;
    latestSampleY = sampleY;
    processed += 1;
  }

  if (traveled + step <= distance) {
    erasing.lastX = latestSampleX;
    erasing.lastY = latestSampleY;
    erasing.pendingX = x;
    erasing.pendingY = y;
    return;
  }

  if (eraseAtPoint(x, y, radiusWorld, erasing.removalContext)) {
    erasing.changed = true;
  }
  erasing.lastX = x;
  erasing.lastY = y;
}

function flushPendingErasePoint(erasing) {
  if (!erasing) {
    return false;
  }

  if (!Number.isFinite(erasing.pendingX) || !Number.isFinite(erasing.pendingY)) {
    return false;
  }

  const x = erasing.pendingX;
  const y = erasing.pendingY;
  erasing.pendingX = NaN;
  erasing.pendingY = NaN;
  eraseAlongPath(erasing, x, y);
  return true;
}

function scheduleEraseFrame() {
  const erasing = state.erasing;
  if (!erasing || erasing.rafId !== null) {
    return;
  }

  erasing.rafId = window.requestAnimationFrame(() => {
    if (!state.erasing || state.erasing !== erasing) {
      return;
    }

    erasing.rafId = null;
    flushPendingErasePoint(erasing);

    if (Number.isFinite(erasing.pendingX) && Number.isFinite(erasing.pendingY)) {
      scheduleEraseFrame();
    }
  });
}

function queueErasePoint(erasing, x, y) {
  if (!erasing) {
    return;
  }
  erasing.pendingX = x;
  erasing.pendingY = y;
  scheduleEraseFrame();
}

function getVisibleStampCount() {
  return state.stampCount;
}

function getSequenceSlotDatasetKey(slotIndex, key) {
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, MAX_LAYER_SEQUENCE_EFFECTS - 1);
  return `sequenceSlot${safeSlotIndex}${key.slice("sequence".length)}`;
}

function deleteSequenceRuntimeDataset(element) {
  if (!element?.dataset) {
    return;
  }
  for (const key of Object.keys(element.dataset)) {
    if (key.startsWith("sequence")) {
      delete element.dataset[key];
    }
  }
}

function loadSequenceSlotScratch(stamp, slotIndex) {
  if (!stamp?.dataset) {
    return;
  }
  for (const key of SEQUENCE_SLOT_STATE_KEYS) {
    delete stamp.dataset[key];
  }
  for (const key of SEQUENCE_SLOT_STATE_KEYS) {
    const slotKey = getSequenceSlotDatasetKey(slotIndex, key);
    if (Object.prototype.hasOwnProperty.call(stamp.dataset, slotKey)) {
      stamp.dataset[key] = stamp.dataset[slotKey];
    }
  }
}

function commitSequenceSlotScratch(stamp, slotIndex) {
  if (!stamp?.dataset) {
    return;
  }
  for (const key of SEQUENCE_SLOT_STATE_KEYS) {
    const slotKey = getSequenceSlotDatasetKey(slotIndex, key);
    if (Object.prototype.hasOwnProperty.call(stamp.dataset, key)) {
      stamp.dataset[slotKey] = stamp.dataset[key];
    } else {
      delete stamp.dataset[slotKey];
    }
    delete stamp.dataset[key];
  }
}

function cloneSequenceRuntime(runtime) {
  if (!runtime || typeof runtime !== "object") {
    return null;
  }
  const clone = { ...runtime };
  if (Array.isArray(runtime.triggeredPulseByIndex)) {
    clone.triggeredPulseByIndex = runtime.triggeredPulseByIndex.slice();
  }
  if (runtime.lastTriggeredIndexByPulse instanceof Map) {
    clone.lastTriggeredIndexByPulse = new Map(runtime.lastTriggeredIndexByPulse);
  }
  if (runtime.triggeredPulseIdsThisFrame instanceof Set) {
    clone.triggeredPulseIdsThisFrame = new Set(runtime.triggeredPulseIdsThisFrame);
  }
  return clone;
}

function createSequenceExportSnapshot() {
  return state.strokes.map((stroke) => ({
    stroke,
    sequenceRuntime: cloneSequenceRuntime(stroke.sequenceRuntime),
    sequenceSlotRuntimes: Array.isArray(stroke.sequenceSlotRuntimes)
      ? stroke.sequenceSlotRuntimes.map(cloneSequenceRuntime)
      : null,
    elements: stroke.elements.map((element) => {
      const dataset = {};
      for (const key of Object.keys(element.dataset)) {
        if (key.startsWith("sequence")) {
          dataset[key] = element.dataset[key];
        }
      }
      return {
        element,
        dataset,
        src: element.getAttribute("src") || "",
        opacity: element.style.opacity,
        transform: element.style.transform,
        filter: element.style.filter
      };
    })
  }));
}

function restoreSequenceExportSnapshot(snapshot) {
  const list = Array.isArray(snapshot) ? snapshot : [];
  for (const strokeSnapshot of list) {
    if (!strokeSnapshot || !strokeSnapshot.stroke) {
      continue;
    }
    strokeSnapshot.stroke.sequenceRuntime = cloneSequenceRuntime(strokeSnapshot.sequenceRuntime);
    strokeSnapshot.stroke.sequenceSlotRuntimes = Array.isArray(strokeSnapshot.sequenceSlotRuntimes)
      ? strokeSnapshot.sequenceSlotRuntimes.map(cloneSequenceRuntime)
      : null;
    const elements = Array.isArray(strokeSnapshot.elements) ? strokeSnapshot.elements : [];
    for (const elementSnapshot of elements) {
      const element = elementSnapshot?.element;
      if (!element) {
        continue;
      }
      deleteSequenceRuntimeDataset(element);
      for (const [key, value] of Object.entries(elementSnapshot.dataset || {})) {
        element.dataset[key] = value;
      }
      if (element.getAttribute("src") !== elementSnapshot.src) {
        element.src = elementSnapshot.src;
      }
      element.style.opacity = elementSnapshot.opacity;
      element.style.transform = elementSnapshot.transform;
      element.style.filter = elementSnapshot.filter || "";
    }
  }
}

function resetSequencesForExport() {
  for (const stroke of state.strokes) {
    resetStrokeSequenceRuntime(stroke);
    for (const element of stroke.elements) {
      resetStampSequenceStyle(element, true);
    }
  }
}

function hasActiveSequenceEffectOnCanvas() {
  return state.strokes.some((stroke) => {
    if (!stroke || stroke.hidden || !isLayerSequenceEnabled(stroke) || !Array.isArray(stroke.elements)) {
      return false;
    }
    return getLayerSequenceSlots(stroke).some((slot) =>
      isImplementedLayerSequenceEffect(slot.effect) &&
        stroke.elements.some((element) => element.parentElement === world)
    );
  });
}

function notifyStampLimitReached() {
  updateBrushStatus(
    `Canvas limit reached (${MAX_VISIBLE_STAMPS.toLocaleString()} images). Undo or clear to add more.`
  );
}

function normalizeStrokeLayerType(layerType) {
  if (layerType === "spray" || layerType === "line" || layerType === "box" || layerType === "circle") {
    return layerType;
  }
  return "stroke";
}

function normalizeLayerSequenceValue(value, options) {
  const allowed = new Set(options.map((option) => option.value));
  const candidate = Array.isArray(value) ? value[0] : value;
  return allowed.has(String(candidate || "")) ? String(candidate) : options[0]?.value || "";
}

function normalizeLayerSequenceSlot(slot = {}) {
  return {
    effect: normalizeLayerSequenceValue(
      slot.effect || slot.sequenceEffect || slot.sequenceEffects,
      LAYER_SEQUENCE_EFFECT_OPTIONS
    ),
    timingStyle: normalizeLayerSequenceValue(
      slot.timingStyle || slot.sequenceTimingStyle || slot.sequenceTimingStyles,
      LAYER_SEQUENCE_TIMING_OPTIONS
    ),
    settings: normalizeLayerSequenceSettings(slot.settings || slot.sequenceSettings)
  };
}

function normalizeExtraLayerSequenceSlots(slots) {
  if (!Array.isArray(slots)) {
    return [];
  }
  return slots.slice(0, MAX_LAYER_SEQUENCE_EFFECTS - 1).map(normalizeLayerSequenceSlot);
}

function getExtraLayerSequenceSlots(stroke) {
  return normalizeExtraLayerSequenceSlots(stroke?.sequenceEffectSlots);
}

function setExtraLayerSequenceSlots(stroke, slots) {
  if (!stroke) {
    return;
  }
  stroke.sequenceEffectSlots = normalizeExtraLayerSequenceSlots(slots);
}

function getLayerSequenceSlotCount(stroke) {
  return 1 + getExtraLayerSequenceSlots(stroke).length;
}

function getLayerSequenceSlots(stroke) {
  return [
    getLayerSequenceSlot(stroke, 0),
    ...getExtraLayerSequenceSlots(stroke)
  ].slice(0, MAX_LAYER_SEQUENCE_EFFECTS);
}

function isImplementedLayerSequenceEffect(effect) {
  return (
    effect === "show-hide" ||
    effect === "move" ||
    effect === "rotate" ||
    effect === "scale" ||
    effect === "color-cycle" ||
    effect === "image-cycle"
  );
}

function getLayerSequenceSlot(stroke, slotIndex = 0) {
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, MAX_LAYER_SEQUENCE_EFFECTS - 1);
  if (safeSlotIndex <= 0) {
    return {
      effect: normalizeLayerSequenceValue(
        stroke?.sequenceEffect || stroke?.sequenceEffects,
        LAYER_SEQUENCE_EFFECT_OPTIONS
      ),
      timingStyle: normalizeLayerSequenceValue(
        stroke?.sequenceTimingStyle || stroke?.sequenceTimingStyles,
        LAYER_SEQUENCE_TIMING_OPTIONS
      ),
      settings: normalizeLayerSequenceSettings(stroke?.sequenceSettings)
    };
  }
  const extras = getExtraLayerSequenceSlots(stroke);
  return normalizeLayerSequenceSlot(extras[safeSlotIndex - 1]);
}

function getLayerSequenceEffect(stroke, slotIndex = 0) {
  if (Number(slotIndex) > 0) {
    return getLayerSequenceSlot(stroke, slotIndex).effect;
  }
  return normalizeLayerSequenceValue(
    stroke?.sequenceEffect || stroke?.sequenceEffects,
    LAYER_SEQUENCE_EFFECT_OPTIONS
  );
}

function getLayerSequenceTimingStyle(stroke, slotIndex = 0) {
  if (Number(slotIndex) > 0) {
    return getLayerSequenceSlot(stroke, slotIndex).timingStyle;
  }
  return normalizeLayerSequenceValue(
    stroke?.sequenceTimingStyle || stroke?.sequenceTimingStyles,
    LAYER_SEQUENCE_TIMING_OPTIONS
  );
}

function isLayerSequenceEnabled(stroke) {
  return stroke ? stroke.sequenceEnabled !== false && stroke.sequenceEnabled === true : false;
}

function setLayerSequenceValue(stroke, group, value, slotIndex = 0) {
  if (!stroke) {
    return;
  }
  const options = group === "timing"
    ? LAYER_SEQUENCE_TIMING_OPTIONS
    : LAYER_SEQUENCE_EFFECT_OPTIONS;
  const normalized = normalizeLayerSequenceValue(value, options);
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, MAX_LAYER_SEQUENCE_EFFECTS - 1);
  if (safeSlotIndex > 0) {
    const extras = getExtraLayerSequenceSlots(stroke);
    const slot = normalizeLayerSequenceSlot(extras[safeSlotIndex - 1]);
    if (group === "timing") {
      slot.timingStyle = normalized;
    } else {
      slot.effect = normalized;
    }
    extras[safeSlotIndex - 1] = slot;
    setExtraLayerSequenceSlots(stroke, extras);
  } else if (group === "timing") {
    stroke.sequenceTimingStyle = normalized;
    delete stroke.sequenceTimingStyles;
  } else {
    stroke.sequenceEffect = normalized;
    delete stroke.sequenceEffects;
  }
}

function getLayerSequenceSettings(stroke, slotIndex = 0) {
  if (Number(slotIndex) > 0) {
    return getLayerSequenceSlot(stroke, slotIndex).settings;
  }
  return normalizeLayerSequenceSettings({
    ...LAYER_SEQUENCE_DEFAULT_SETTINGS,
    ...(stroke && typeof stroke.sequenceSettings === "object" && stroke.sequenceSettings
      ? stroke.sequenceSettings
      : {})
  });
}

function normalizeLayerSequenceSettings(settings) {
  const normalized = {
    ...LAYER_SEQUENCE_DEFAULT_SETTINGS,
    ...(settings && typeof settings === "object" ? settings : {})
  };
  normalized.showHideFade = Boolean(normalized.showHideFade);
  normalized.imageCycleRandom = Boolean(normalized.imageCycleRandom);
  normalized.moveInstant = Boolean(normalized.moveInstant);
  normalized.showHideFadeLength = clamp(Math.round(Number(normalized.showHideFadeLength) || 300), 0, 3000);
  normalized.moveMode = LAYER_SEQUENCE_MOVE_MODE_OPTIONS.some((option) => option.value === normalized.moveMode)
    ? normalized.moveMode
    : "left";
  normalized.moveStrength = Number.isFinite(Number(normalized.moveStrength))
    ? clamp(Math.round(Number(normalized.moveStrength)), 0, 1000)
    : 80;
  normalized.moveSpeed = normalizeSequenceSpeedSliderValue(normalized.moveSpeed, 4000, 50, 45);
  normalized.colorCycleColor = normalizeHexColor(normalized.colorCycleColor, "#ff00ff");
  normalized.colorCycleAmount = Number.isFinite(Number(normalized.colorCycleAmount))
    ? clamp(Math.round(Number(normalized.colorCycleAmount)), 0, 100)
    : 70;
  normalized.colorCycleInstant = Boolean(normalized.colorCycleInstant);
  normalized.colorCycleSpeed = normalizeSequenceSpeedSliderValue(normalized.colorCycleSpeed, 5000, 50, 45);
  normalized.rotateSpeed = Number.isFinite(Number(normalized.rotateSpeed))
    ? clamp(Math.round(Number(normalized.rotateSpeed)), 1, 100)
    : 45;
  normalized.rotateContinuous = Boolean(normalized.rotateContinuous);
  normalized.rotateReverse = Boolean(normalized.rotateReverse);
  normalized.scaleSpeed = normalizeSequenceSpeedSliderValue(normalized.scaleSpeed, 6000, 100, 45);
  normalized.scaleAmount = clamp(Math.round(Number(normalized.scaleAmount) || 50), 0, 300);
  normalized.imageCycleSpeed = normalizeSequenceSpeedSliderValue(normalized.imageCycleSpeed, 4000, 50, 50);
  normalized.pulseSpeed = Number.isFinite(Number(normalized.pulseSpeed))
    ? clamp(Math.round(Number(normalized.pulseSpeed)), 1, 500)
    : 35;
  normalized.pulseRate = Number.isFinite(Number(normalized.pulseRate))
    ? clamp(Math.round(Number(normalized.pulseRate)), 1, 300)
    : 35;
  normalized.waveSpeed = normalizeSequenceSpeedSliderValue(normalized.waveSpeed, 2000, 20, 45);
  normalized.waveReverse = Boolean(normalized.waveReverse);
  normalized.stepLength = clamp(Math.round(Number(normalized.stepLength) || 350), 50, 4000);
  normalized.stepAmount = clamp(Math.round(Number(normalized.stepAmount) || 1), 1, 200);
  normalized.randomSpeed = normalizeSequenceSpeedSliderValue(normalized.randomSpeed, 4000, 50, 45);
  return normalized;
}

function setLayerSequenceSetting(stroke, key, rawValue, slotIndex = 0) {
  if (!stroke || !(key in LAYER_SEQUENCE_DEFAULT_SETTINGS)) {
    return;
  }
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, MAX_LAYER_SEQUENCE_EFFECTS - 1);
  const nextSettings = getLayerSequenceSettings(stroke, safeSlotIndex);
  if (typeof LAYER_SEQUENCE_DEFAULT_SETTINGS[key] === "boolean") {
    nextSettings[key] = Boolean(rawValue);
  } else if (typeof LAYER_SEQUENCE_DEFAULT_SETTINGS[key] === "string") {
    nextSettings[key] = String(rawValue || "");
  } else {
    nextSettings[key] = Number(rawValue);
  }
  if (safeSlotIndex > 0) {
    const extras = getExtraLayerSequenceSlots(stroke);
    const slot = normalizeLayerSequenceSlot(extras[safeSlotIndex - 1]);
    slot.settings = normalizeLayerSequenceSettings(nextSettings);
    extras[safeSlotIndex - 1] = slot;
    setExtraLayerSequenceSlots(stroke, extras);
  } else {
    stroke.sequenceSettings = normalizeLayerSequenceSettings(nextSettings);
  }
}

function createLayerSequenceSelect(stroke, group, options, slotIndex = 0) {
  const selectedValue = group === "timing"
    ? getLayerSequenceTimingStyle(stroke, slotIndex)
    : getLayerSequenceEffect(stroke, slotIndex);
  const select = document.createElement("select");
  select.className = "edit-layer-sequence-select";
  select.dataset.sequenceGroup = group;
  select.dataset.sequenceSlotIndex = String(slotIndex);
  select.setAttribute("aria-label", group === "timing" ? "Sequence style" : "Sequence effect");

  for (const option of options) {
    const optionNode = document.createElement("option");
    optionNode.value = option.value;
    optionNode.textContent = option.label;
    optionNode.selected = option.value === selectedValue;
    select.appendChild(optionNode);
  }

  return select;
}

function createLayerSequenceToggleControl(stroke, key, label, slotIndex = 0) {
  const settings = getLayerSequenceSettings(stroke, slotIndex);
  const field = document.createElement("label");
  field.className = "edit-layer-sequence-setting edit-layer-sequence-toggle";

  const text = document.createElement("span");
  text.textContent = label;
  const input = document.createElement("input");
  input.type = "checkbox";
  input.className = "edit-layer-sequence-setting-input";
  input.dataset.sequenceSetting = key;
  input.dataset.sequenceSettingType = "boolean";
  input.dataset.sequenceSlotIndex = String(slotIndex);
  input.checked = Boolean(settings[key]);
  const switchControl = document.createElement("span");
  switchControl.className = "ios-switch edit-layer-sequence-switch";
  const switchSlider = document.createElement("span");
  switchSlider.className = "ios-switch-slider";
  switchSlider.setAttribute("aria-hidden", "true");
  switchControl.appendChild(input);
  switchControl.appendChild(switchSlider);

  field.appendChild(text);
  field.appendChild(switchControl);
  return field;
}

function getCompressedSequenceSliderConfig(key) {
  if (key === "imageCycleSpeed") {
    return { min: 1, knee: 75, max: 100, kneePosition: 50 };
  }
  if (key === "pulseSpeed") {
    return { min: 1, knee: 100, max: 500, kneePosition: 67 };
  }
  if (key === "pulseRate") {
    return { min: 1, knee: 100, max: 300, kneePosition: 67 };
  }
  return null;
}

function mapSequenceSettingToSliderPosition(key, value) {
  const config = getCompressedSequenceSliderConfig(key);
  if (!config) {
    return Number(value);
  }
  const numericValue = clamp(Number(value) || config.min, config.min, config.max);
  if (numericValue <= config.knee) {
    return Math.round(
      1 + ((numericValue - config.min) / (config.knee - config.min)) * (config.kneePosition - 1)
    );
  }
  return Math.round(
    config.kneePosition +
      ((numericValue - config.knee) / (config.max - config.knee)) * (100 - config.kneePosition)
  );
}

function mapSequenceSliderPositionToSetting(key, value) {
  const config = getCompressedSequenceSliderConfig(key);
  if (!config) {
    return Number(value);
  }
  const sliderValue = clamp(Number(value) || 1, 1, 100);
  if (sliderValue <= config.kneePosition) {
    return Math.round(
      config.min +
        ((sliderValue - 1) / (config.kneePosition - 1)) * (config.knee - config.min)
    );
  }
  return Math.round(
    config.knee +
      ((sliderValue - config.kneePosition) / (100 - config.kneePosition)) * (config.max - config.knee)
  );
}

function getSequenceSettingInputValue(input) {
  if (!input || input.dataset.sequenceSettingType !== "number") {
    return input?.value;
  }
  return mapSequenceSliderPositionToSetting(input.dataset.sequenceSetting || "", input.value);
}

function createLayerSequenceRangeControl(stroke, key, label, min, max, step, suffix = "", slotIndex = 0) {
  const settings = getLayerSequenceSettings(stroke, slotIndex);
  const compressedSlider = getCompressedSequenceSliderConfig(key);
  const field = document.createElement("label");
  field.className = "edit-layer-sequence-setting edit-layer-sequence-range";

  const labelText = document.createElement("span");
  labelText.className = "edit-layer-sequence-setting-label";
  labelText.textContent = label;

  const value = document.createElement("span");
  value.className = "edit-layer-sequence-setting-value";
  value.textContent = `${settings[key]}${suffix}`;

  const input = document.createElement("input");
  input.type = "range";
  input.className = "edit-layer-sequence-setting-input";
  input.dataset.sequenceSetting = key;
  input.dataset.sequenceSettingType = "number";
  input.dataset.sequenceSlotIndex = String(slotIndex);
  input.min = compressedSlider ? "1" : String(min);
  input.max = compressedSlider ? "100" : String(max);
  input.step = compressedSlider ? "1" : String(step);
  input.value = String(compressedSlider ? mapSequenceSettingToSliderPosition(key, settings[key]) : settings[key]);

  field.appendChild(labelText);
  field.appendChild(value);
  field.appendChild(input);
  return field;
}

function createLayerSequenceColorControl(stroke, key, label, slotIndex = 0) {
  const settings = getLayerSequenceSettings(stroke, slotIndex);
  const field = document.createElement("label");
  field.className = "edit-layer-sequence-setting edit-layer-sequence-color";

  const labelText = document.createElement("span");
  labelText.className = "edit-layer-sequence-setting-label";
  labelText.textContent = label;

  const input = document.createElement("input");
  input.type = "color";
  input.className = "edit-layer-sequence-setting-input";
  input.dataset.sequenceSetting = key;
  input.dataset.sequenceSettingType = "string";
  input.dataset.sequenceSlotIndex = String(slotIndex);
  input.value = normalizeHexColor(settings[key], "#ff00ff");

  field.appendChild(labelText);
  field.appendChild(input);
  return field;
}

function createLayerSequenceOptionControl(stroke, key, label, options, slotIndex = 0) {
  const settings = getLayerSequenceSettings(stroke, slotIndex);
  const field = document.createElement("label");
  field.className = "edit-layer-sequence-setting edit-layer-sequence-option";

  const labelText = document.createElement("span");
  labelText.className = "edit-layer-sequence-setting-label";
  labelText.textContent = label;

  const select = document.createElement("select");
  select.className =
    "edit-layer-sequence-setting-input edit-layer-sequence-select edit-layer-sequence-setting-select";
  select.dataset.sequenceSetting = key;
  select.dataset.sequenceSettingType = "string";
  select.dataset.sequenceSlotIndex = String(slotIndex);

  for (const option of options) {
    const optionNode = document.createElement("option");
    optionNode.value = option.value;
    optionNode.textContent = option.label;
    optionNode.selected = option.value === settings[key];
    select.appendChild(optionNode);
  }

  field.appendChild(labelText);
  field.appendChild(select);
  return field;
}

function createLayerSequenceSettings(stroke, slotIndex = 0) {
  const effect = getLayerSequenceEffect(stroke, slotIndex);
  const timingStyle = getLayerSequenceTimingStyle(stroke, slotIndex);
  const settings = getLayerSequenceSettings(stroke, slotIndex);
  const panel = document.createElement("div");
  panel.className = "edit-layer-sequence-settings";
  panel.dataset.strokeId = String(stroke.id);
  panel.dataset.sequenceSlotIndex = String(slotIndex);

  if (effect === "show-hide") {
    panel.appendChild(createLayerSequenceToggleControl(stroke, "showHideFade", "fade?", slotIndex));
    if (settings.showHideFade) {
      panel.appendChild(
        createLayerSequenceRangeControl(stroke, "showHideFadeLength", "fade length", 0, 3000, 50, "ms", slotIndex)
      );
    }
  } else if (effect === "move") {
    panel.appendChild(createLayerSequenceToggleControl(stroke, "moveInstant", "instant?", slotIndex));
    panel.appendChild(
      createLayerSequenceOptionControl(stroke, "moveMode", "mode", LAYER_SEQUENCE_MOVE_MODE_OPTIONS, slotIndex)
    );
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "moveStrength", "movement strength", 0, 1000, 5, "px", slotIndex)
    );
    const moveSpeedControl = createLayerSequenceRangeControl(
      stroke,
      "moveSpeed",
      "movement speed",
      1,
      100,
      1,
      "",
      slotIndex
    );
    if (settings.moveInstant && settings.moveMode !== "circle") {
      moveSpeedControl.classList.add("is-disabled");
      const moveSpeedInput = moveSpeedControl.querySelector("input");
      if (moveSpeedInput) {
        moveSpeedInput.disabled = true;
      }
    }
    panel.appendChild(moveSpeedControl);
  } else if (effect === "rotate") {
    panel.appendChild(createLayerSequenceToggleControl(stroke, "rotateContinuous", "continuous?", slotIndex));
    panel.appendChild(createLayerSequenceToggleControl(stroke, "rotateReverse", "reverse?", slotIndex));
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "rotateSpeed", "rotate speed", 1, 100, 1, "", slotIndex)
    );
  } else if (effect === "scale") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "scaleSpeed", "scale speed", 1, 100, 1, "", slotIndex)
    );
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "scaleAmount", "scale amount", 0, 300, 5, "%", slotIndex)
    );
  } else if (effect === "image-cycle") {
    panel.appendChild(createLayerSequenceToggleControl(stroke, "imageCycleRandom", "random?", slotIndex));
    if (timingStyle === "all") {
      panel.appendChild(
        createLayerSequenceRangeControl(stroke, "imageCycleSpeed", "speed", 1, 100, 1, "", slotIndex)
      );
    }
  } else if (effect === "color-cycle") {
    panel.appendChild(createLayerSequenceColorControl(stroke, "colorCycleColor", "color", slotIndex));
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "colorCycleAmount", "hue shift amount", 0, 100, 1, "%", slotIndex)
    );
    panel.appendChild(createLayerSequenceToggleControl(stroke, "colorCycleInstant", "instant?", slotIndex));
    const colorSpeedControl = createLayerSequenceRangeControl(
      stroke,
      "colorCycleSpeed",
      "speed",
      1,
      100,
      1,
      "",
      slotIndex
    );
    if (settings.colorCycleInstant) {
      colorSpeedControl.classList.add("is-disabled");
      const colorSpeedInput = colorSpeedControl.querySelector("input");
      if (colorSpeedInput) {
        colorSpeedInput.disabled = true;
      }
    }
    panel.appendChild(colorSpeedControl);
  }

  if (timingStyle === "pulse") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "pulseSpeed", "pulse speed", 1, 500, 1, "", slotIndex)
    );
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "pulseRate", "pulse rate", 1, 300, 1, "", slotIndex)
    );
  } else if (timingStyle === "wave") {
    panel.appendChild(createLayerSequenceToggleControl(stroke, "waveReverse", "reverse?", slotIndex));
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "waveSpeed", "bounce speed", 1, 100, 1, "", slotIndex)
    );
  } else if (timingStyle === "step") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "stepLength", "step length", 50, 4000, 50, "ms", slotIndex)
    );
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "stepAmount", "step amount", 1, 200, 1, "", slotIndex)
    );
  } else if (timingStyle === "random") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "randomSpeed", "randomization speed", 1, 100, 1, "", slotIndex)
    );
  }

  return panel;
}

function createLayerSequenceAddRemoveRow(stroke, slotIndex, slotCount) {
  const canAdd = slotIndex === slotCount - 1 && slotCount < MAX_LAYER_SEQUENCE_EFFECTS;
  const canRemove = slotIndex > 0;
  if (!canAdd && !canRemove) {
    return null;
  }

  const row = document.createElement("div");
  row.className = "edit-layer-sequence-add-row";
  row.dataset.strokeId = String(stroke.id);
  row.dataset.sequenceSlotIndex = String(slotIndex);
  row.classList.toggle("has-add", canAdd);
  row.classList.toggle("has-remove", canRemove);

  if (canAdd) {
    const addButton = document.createElement("button");
    addButton.type = "button";
    addButton.className = "edit-layer-sequence-add-button";
    addButton.dataset.layerAction = "sequence-add-effect";
    addButton.textContent = "+";
    addButton.title = "Add layer effect";
    addButton.setAttribute("aria-label", addButton.title);
    row.appendChild(addButton);
  }

  if (canRemove) {
    const removeButton = document.createElement("button");
    removeButton.type = "button";
    removeButton.className = "edit-layer-sequence-remove-button";
    removeButton.dataset.layerAction = "sequence-remove-effect";
    removeButton.dataset.sequenceSlotIndex = String(slotIndex);
    removeButton.title = "Remove layer effect";
    removeButton.setAttribute("aria-label", removeButton.title);
    const icon = document.createElement("img");
    icon.src = "bomb.png";
    icon.alt = "";
    icon.setAttribute("aria-hidden", "true");
    removeButton.appendChild(icon);
    row.appendChild(removeButton);
  }

  return row;
}

function serializeStrokeList(strokes) {
  return strokes.map((stroke) => ({
    id: Number.isFinite(Number(stroke.id)) ? Number(stroke.id) : null,
    layerNumber: Number.isFinite(Number(stroke.layerNumber)) ? Number(stroke.layerNumber) : null,
    layerType: normalizeStrokeLayerType(stroke.layerType),
    brushCategoryName: typeof stroke.brushCategoryName === "string"
      ? stroke.brushCategoryName
      : "",
    animationPaused: Boolean(stroke.animationPaused),
    sequenceOpen: Boolean(stroke.sequenceOpen),
    sequenceEnabled: isLayerSequenceEnabled(stroke),
    sequenceEffect: getLayerSequenceEffect(stroke),
    sequenceTimingStyle: getLayerSequenceTimingStyle(stroke),
    sequenceSettings: normalizeLayerSequenceSettings(stroke.sequenceSettings),
    sequenceEffectSlots: getExtraLayerSequenceSlots(stroke),
    stamps: stroke.elements.map((element) => ({
      // Persist only layout/render metadata and brush linkage for compact reloads.
      brushId: Number(element.dataset.brushId) || null,
      left: parseFloat(element.style.left) || 0,
      top: parseFloat(element.style.top) || 0,
      width: parseFloat(element.style.width) || 0,
      height: parseFloat(element.style.height) || 0,
      rotation: Number(element.dataset.rotation) || 0,
      opacity: Number.isFinite(Number(element.dataset.sequenceBaseOpacity))
        ? clamp(Number(element.dataset.sequenceBaseOpacity), 0, 1)
        : Number.isFinite(Number(element.style.opacity))
        ? clamp(Number(element.style.opacity), 0, 1)
        : 1,
      imageRendering: element.style.imageRendering === "auto" ? "auto" : "pixelated",
      tintColor: normalizeHexColor(element.dataset.tintColor, "#ffffff"),
      tintAmount: clamp(Number(element.dataset.tintAmount) || 0, 0, 100)
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
    selectedBrushIds: state.selectedBrushIds instanceof Set
      ? Array.from(state.selectedBrushIds)
          .map((id) => Number(id))
          .filter((id) => Number.isFinite(id))
      : [],
    activeStockBrushFolderId: typeof state.activeStockBrushFolderId === "string"
      ? state.activeStockBrushFolderId
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
      spacing: getSpacingValue(),
      rotation: parseNumericInputValue(rotationSlider, 0),
      opacity: parseNumericInputValue(opacitySlider, 100),
      tintColor: normalizeHexColor(tintColorInput.value),
      tintAmount: parseNumericInputValue(tintAmountSlider, 0),
      renderLinear: renderModeToggle.checked,
      brushPreviewEnabled: state.brushPreviewEnabled !== false,
      cursorTrailEnabled: cursorTrailToggle.checked,
      cursorTrailCount: parseNumericInputValue(cursorTrailCountSlider, 24),
      drawMode: state.drawMode,
      spraySpread: parseNumericInputValue(spraySpreadSlider, DEFAULT_SPRAY_SPREAD),
      sidebarCollapsed: state.sidebarCollapsed,
      sidebarTab: state.sidebarTab === "export" ? "draw" : state.sidebarTab,
      brushGalleryCollapsed: state.brushGalleryCollapsed,
      brushGallerySort: normalizeBrushGallerySort(state.brushGallerySort),
      customBrushPresetSources: getCustomBrushPresetSourcesSnapshot(),
      activeCustomBrushPresetIndex: normalizeCustomBrushPresetIndex(state.activeCustomBrushPresetIndex),
      canvasBackgroundColor: normalizeHexColor(state.canvasBackgroundColor, "#ffffff"),
      exportBackgroundEnabled: state.exportBackgroundEnabled !== false,
      exportSeeBeyondEnabled: state.exportSeeBeyondEnabled !== false,
      exportBgImageUrl: typeof state.exportBgImageUrl === "string" &&
        state.exportBgImageUrl.startsWith("data:image/")
        ? state.exportBgImageUrl
        : "",
      exportBgImageOpacity: clamp(Number(state.exportBgImageOpacity) || 0, 0, 100),
      exportBgImageMode: state.exportBgImageMode === "tile" ? "tile" : "stretch",
      exportBgImageTileSize: normalizeExportBgTileSize(state.exportBgImageTileSize),
      exportBgImageNaturalWidth: Math.max(0, Number(state.exportBgImageNaturalWidth) || 0),
      exportBgImageNaturalHeight: Math.max(0, Number(state.exportBgImageNaturalHeight) || 0),
      lastExportSetup: normalizeExportSetupSnapshot(state.lastExportSetup),
      exportAnimationAuto: state.exportAnimationAuto !== false,
      exportAnimationSeconds: Number(state.exportAnimationSeconds) || 1,
      exportAnimationFrameCount: String(state.exportAnimationFrameCount || ""),
      exportVideoAuto: state.exportVideoAuto !== false,
      exportVideoSeconds: Number(state.exportVideoSeconds) || 3,
      showGifCountIndicator: state.showGifCountIndicator !== false,
      showGifPauseButton: state.showGifPauseButton !== false,
      showDrawBackgroundColorControl: Boolean(state.showDrawBackgroundColorControl),
      collapsedSliderGroups: getCollapsedSliderGroupSnapshot()
    },
    brushes: state.brushes.map((brush) => ({
      id: brush.id,
      url: brush.url,
      name: brush.name,
      width: brush.width,
      height: brush.height,
      originalUrl: brush.originalUrl || brush.url,
      originalWidth: brush.originalWidth || brush.width,
      originalHeight: brush.originalHeight || brush.height,
      frameCount: normalizeBrushFrameCount(brush.frameCount),
      frameRange: brush.frameRange && Number.isFinite(Number(brush.frameRange.end))
        ? {
            start: Math.max(0, Math.floor(Number(brush.frameRange.start) || 0)),
            end: Math.max(1, Math.floor(Number(brush.frameRange.end) || 1))
          }
        : null,
      cropRect: brush.cropRect && Number.isFinite(Number(brush.cropRect.width))
        ? {
            x: Number(brush.cropRect.x) || 0,
            y: Number(brush.cropRect.y) || 0,
            width: Math.max(1, Number(brush.cropRect.width) || brush.width),
            height: Math.max(1, Number(brush.cropRect.height) || brush.height)
          }
        : null,
      enabled: brush.enabled,
      weightMode: normalizeBrushWeightMode(brush.weightMode)
    })),
    strokeBrushes: collectStrokeBrushSources(),
    strokes: serializeStrokeList(state.strokes),
    redoStrokes: serializeStrokeList(getRedoDrawStrokes())
  };
}

function getSnapshotStampCount(snapshot) {
  const strokes = Array.isArray(snapshot?.strokes) ? snapshot.strokes : [];
  return strokes.reduce((total, stroke) => {
    const stamps = Array.isArray(stroke?.stamps) ? stroke.stamps.length : 0;
    return total + stamps;
  }, 0);
}

function fitBoundsToAspect(bounds, aspectRatio) {
  const normalized = normalizeExportSelectionBounds(bounds);
  const width = Math.max(EXPORT_MIN_SIZE, normalized.right - normalized.left);
  const height = Math.max(EXPORT_MIN_SIZE, normalized.bottom - normalized.top);
  const centerX = (normalized.left + normalized.right) / 2;
  const centerY = (normalized.top + normalized.bottom) / 2;
  let nextWidth = width;
  let nextHeight = height;

  if (width / height > aspectRatio) {
    nextHeight = width / aspectRatio;
  } else {
    nextWidth = height * aspectRatio;
  }

  return normalizeExportSelectionBounds({
    left: centerX - nextWidth / 2,
    right: centerX + nextWidth / 2,
    top: centerY - nextHeight / 2,
    bottom: centerY + nextHeight / 2
  });
}

async function createSavedCompositionThumbnail() {
  const outputWidth = 240;
  const outputHeight = 150;
  restoreAllCulledStampSources();
  const bounds = fitBoundsToAspect(computeInitialExportSelectionBounds(), outputWidth / outputHeight);
  const entries = await collectExportStampEntries(bounds);
  const canvas = document.createElement("canvas");
  canvas.width = outputWidth;
  canvas.height = outputHeight;
  const ctx = canvas.getContext("2d", { alpha: true });
  if (!ctx) {
    return "";
  }
  await drawExportFrameAsync(
    ctx,
    bounds,
    outputWidth,
    outputHeight,
    entries,
    null,
    0,
    {
      includeBackground: true,
      backgroundColor: state.canvasBackgroundColor
    }
  );
  return canvas.toDataURL("image/png");
}

function formatSavedCompositionDate(timestamp) {
  try {
    return new Intl.DateTimeFormat(undefined, {
      month: "short",
      day: "numeric",
      hour: "numeric",
      minute: "2-digit"
    }).format(new Date(timestamp));
  } catch (error) {
    return "saved scene";
  }
}

function renderSavedCompositionsGallery() {
  if (!savedCompositionsGallery) {
    return;
  }

  savedCompositionsGallery.innerHTML = "";
  if (!state.savedCompositions.length) {
    const empty = document.createElement("p");
    empty.className = "empty-panel-label";
    empty.textContent = state.savedCompositionsLoaded ? "no saved compositions" : "loading saved compositions";
    savedCompositionsGallery.appendChild(empty);
    return;
  }

  const fragment = document.createDocumentFragment();
  for (const entry of state.savedCompositions) {
    const card = document.createElement("div");
    card.className = "saved-composition-card";
    card.dataset.savedCompositionId = entry.id;

    const loadButton = document.createElement("button");
    loadButton.type = "button";
    loadButton.className = "saved-composition-load-button";
    loadButton.title = "Load saved composition";

    const preview = document.createElement("div");
    preview.className = "saved-composition-preview";
    if (entry.thumbnailUrl) {
      const image = document.createElement("img");
      image.src = entry.thumbnailUrl;
      image.alt = "";
      image.draggable = false;
      preview.appendChild(image);
    }

    const title = document.createElement("span");
    title.className = "saved-composition-title";
    title.textContent = formatSavedCompositionDate(entry.savedAt);

    const meta = document.createElement("span");
    meta.className = "saved-composition-meta";
    meta.textContent =
      `${entry.stampCount.toLocaleString()} image${entry.stampCount === 1 ? "" : "s"} · ${entry.stockCategory}`;

    const deleteButton = document.createElement("button");
    deleteButton.type = "button";
    deleteButton.className = "saved-composition-delete-button";
    deleteButton.dataset.savedCompositionDeleteId = entry.id;
    deleteButton.title = "Delete saved composition";
    deleteButton.setAttribute("aria-label", "Delete saved composition");
    const deleteIcon = document.createElement("img");
    deleteIcon.src = "bomb.png";
    deleteIcon.alt = "";
    deleteIcon.draggable = false;
    deleteButton.appendChild(deleteIcon);

    loadButton.appendChild(preview);
    loadButton.appendChild(title);
    loadButton.appendChild(meta);
    card.appendChild(loadButton);
    card.appendChild(deleteButton);
    fragment.appendChild(card);
  }
  savedCompositionsGallery.appendChild(fragment);
}

async function loadSavedCompositions() {
  state.savedCompositionsLoaded = false;
  renderSavedCompositionsGallery();
  state.savedCompositions = await getSavedCompositionIndex();
  state.savedCompositionsLoaded = true;
  renderSavedCompositionsGallery();
}

function setSavedCompositionsStatus(message) {
  if (savedCompositionsStatus) {
    savedCompositionsStatus.textContent = message || "";
  }
}

async function saveCurrentComposition() {
  if (!saveCompositionButton) {
    return;
  }

  saveCompositionButton.disabled = true;
  setSavedCompositionsStatus("saving...");
  try {
    const snapshot = buildSessionSnapshot();
    const snapshotJson = JSON.stringify(snapshot);
    const savedAt = Date.now();
    const id = `${savedAt}-${Math.random().toString(36).slice(2, 8)}`;
    const currentIndex = state.savedCompositionsLoaded
      ? state.savedCompositions
      : await getSavedCompositionIndex();
    let thumbnailUrl = "";
    try {
      thumbnailUrl = await createSavedCompositionThumbnail();
    } catch (error) {
      thumbnailUrl = "";
    }
    const entry = {
      id,
      savedAt,
      stampCount: getSnapshotStampCount(snapshot),
      brushCount: Array.isArray(snapshot.brushes) ? snapshot.brushes.length : 0,
      thumbnailUrl,
      stockCategory:
        typeof snapshot.activeStockBrushFolderId === "string" && snapshot.activeStockBrushFolderId
          ? snapshot.activeStockBrushFolderId
          : "custom"
    };
    const nextIndex = [entry, ...currentIndex].sort(
      (left, right) => Number(right.savedAt) - Number(left.savedAt)
    );
    await writeSnapshotToIndexedDb(`${SAVED_COMPOSITION_KEY_PREFIX}${id}`, snapshotJson);
    await writeSavedCompositionIndex(nextIndex);
    state.savedCompositions = nextIndex;
    state.savedCompositionsLoaded = true;
    renderSavedCompositionsGallery();
    setSavedCompositionsStatus("saved");
  } catch (error) {
    setSavedCompositionsStatus("could not save");
  } finally {
    saveCompositionButton.disabled = false;
  }
}

async function loadSavedComposition(id) {
  if (!id) {
    return;
  }

  setSavedCompositionsStatus("loading...");
  try {
    const snapshotJson = await readSnapshotFromIndexedDb(`${SAVED_COMPOSITION_KEY_PREFIX}${id}`);
    if (!snapshotJson) {
      setSavedCompositionsStatus("missing saved scene");
      return;
    }
    if (state.saveTimerId !== null) {
      window.clearTimeout(state.saveTimerId);
      state.saveTimerId = null;
    }
    try {
      sessionStorage.setItem(SESSION_STORAGE_KEY, snapshotJson);
      removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    } catch (error) {
      removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
      setSessionStorageItemSafe(
        SESSION_STORAGE_POINTER_KEY,
        `${SESSION_IDB_PREFIX}${SAVED_COMPOSITION_KEY_PREFIX}${id}`
      );
    }
    await yieldToMainThread();
    const restored = await restoreSessionState(snapshotJson);
    if (!restored) {
      setSavedCompositionsStatus("could not load");
      return;
    }
    setSavedCompositionsStatus("loaded");
  } catch (error) {
    setSavedCompositionsStatus("could not load");
  }
}

function openSavedDeleteConfirmModal(id) {
  if (!savedDeleteConfirmModal || !id) {
    return;
  }
  state.pendingSavedCompositionDeleteId = id;
  savedDeleteConfirmModal.classList.add("is-open");
  savedDeleteConfirmModal.setAttribute("aria-hidden", "false");
  if (savedDeleteConfirmNoButton) {
    savedDeleteConfirmNoButton.focus();
  }
}

function closeSavedDeleteConfirmModal() {
  if (!savedDeleteConfirmModal) {
    return;
  }
  state.pendingSavedCompositionDeleteId = null;
  savedDeleteConfirmModal.classList.remove("is-open");
  savedDeleteConfirmModal.setAttribute("aria-hidden", "true");
}

async function confirmDeleteSavedComposition() {
  const id = state.pendingSavedCompositionDeleteId;
  if (!id) {
    closeSavedDeleteConfirmModal();
    return;
  }

  setSavedCompositionsStatus("deleting...");
  try {
    const nextIndex = state.savedCompositions.filter((entry) => entry.id !== id);
    await deleteSnapshotFromIndexedDb(`${SAVED_COMPOSITION_KEY_PREFIX}${id}`);
    await writeSavedCompositionIndex(nextIndex);
    state.savedCompositions = nextIndex;
    state.savedCompositionsLoaded = true;
    renderSavedCompositionsGallery();
    setSavedCompositionsStatus("deleted");
  } catch (error) {
    setSavedCompositionsStatus("could not delete");
  } finally {
    closeSavedDeleteConfirmModal();
  }
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

function createStampElement(stampData, brush, fallbackTintSettings = null) {
  const width = Math.max(1, Number(stampData.width) || brush.width);
  const height = Math.max(1, Number(stampData.height) || brush.height);
  const stamp = document.createElement("img");

  stamp.className = "stamp";
  stamp.src = brush.url;
  markGifPlaybackStart(stamp, brush.url);
  stamp.alt = "";
  stamp.draggable = false;
  stamp.loading = "lazy";
  stamp.decoding = "async";
  stamp.dataset.brushUrl = brush.url;
  stamp.dataset.brushId = String(brush.id);
  applyGifPauseStateToImage(stamp);
  stamp.style.width = `${width}px`;
  stamp.style.height = `${height}px`;
  stamp.style.left = `${Number(stampData.left) || 0}px`;
  stamp.style.top = `${Number(stampData.top) || 0}px`;
  const opacity = Number(stampData.opacity);
  const rotation = Number(stampData.rotation) || 0;
  stamp.dataset.rotation = String(rotation);
  stamp.style.opacity = String(Number.isFinite(opacity) ? clamp(opacity, 0, 1) : 1);
  stamp.dataset.sequenceBaseOpacity = stamp.style.opacity;
  stamp.dataset.sequenceBaseSrc = brush.url;
  stamp.style.imageRendering = stampData.imageRendering === "auto" ? "auto" : "pixelated";
  stamp.style.transform = `rotate(${rotation}deg)`;
  const hasSerializedTint =
    stampData &&
    (typeof stampData.tintColor === "string" || Number.isFinite(Number(stampData.tintAmount)));
  const tintSettings = hasSerializedTint
    ? normalizeTintSettings({
        color: stampData.tintColor,
        amountPercent: stampData.tintAmount
      })
    : normalizeTintSettings(fallbackTintSettings, getCurrentTintSettings());
  setElementTintData(stamp, tintSettings);
  applyBrushTintStyle(stamp, false, tintSettings);

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

function restoreStrokeList(serializedStrokes, brushById, appendToWorld, fallbackTintSettings = null) {
  const restored = [];
  const list = Array.isArray(serializedStrokes) ? serializedStrokes : [];
  const fragment = appendToWorld ? document.createDocumentFragment() : null;
  const restoredStampRefs = appendToWorld ? [] : null;

  for (const strokeData of list) {
    const snapshotStrokeId = Number(strokeData?.id);
    const strokeId = Number.isFinite(snapshotStrokeId) ? snapshotStrokeId : state.nextStrokeId;
    const stroke = {
      id: strokeId,
      layerNumber: Number.isFinite(Number(strokeData?.layerNumber))
        ? Number(strokeData.layerNumber)
        : strokeId,
      layerType: normalizeStrokeLayerType(strokeData?.layerType),
	      brushCategoryName:
	        typeof strokeData?.brushCategoryName === "string" && strokeData.brushCategoryName.trim()
	          ? strokeData.brushCategoryName.trim()
	          : "custom",
	      animationPaused: Boolean(strokeData?.animationPaused),
	      sequenceOpen: Boolean(strokeData?.sequenceOpen),
	      sequenceEnabled:
	        typeof strokeData?.sequenceEnabled === "boolean"
	          ? strokeData.sequenceEnabled
	          : Boolean(strokeData?.sequenceOpen),
	      sequenceEffect: normalizeLayerSequenceValue(
	        strokeData?.sequenceEffect || strokeData?.sequenceEffects,
	        LAYER_SEQUENCE_EFFECT_OPTIONS
	      ),
	      sequenceTimingStyle: normalizeLayerSequenceValue(
	        strokeData?.sequenceTimingStyle || strokeData?.sequenceTimingStyles,
	        LAYER_SEQUENCE_TIMING_OPTIONS
	      ),
	      sequenceSettings: normalizeLayerSequenceSettings(strokeData?.sequenceSettings),
	      sequenceEffectSlots: normalizeExtraLayerSequenceSlots(strokeData?.sequenceEffectSlots),
	      elements: []
	    };
    if (strokeId >= state.nextStrokeId) {
      state.nextStrokeId = strokeId + 1;
    }
    const stamps = Array.isArray(strokeData?.stamps) ? strokeData.stamps : [];
    for (const stampData of stamps) {
      const brush = resolveBrushForStamp(stampData, brushById);
      if (!brush) {
        continue;
      }

      const stamp = createStampElement(stampData, brush, fallbackTintSettings);
      stamp.dataset.strokeId = String(stroke.id);
      if (appendToWorld) {
        fragment.appendChild(stamp);
        state.stampCount += 1;
        cacheStampWorldBounds(stamp);
        incrementUrlRef(brush.url);
        restoredStampRefs.push(stamp);
      }
      stroke.elements.push(stamp);
    }

    if (stroke.elements.length) {
      restored.push(stroke);
    }
  }

  if (appendToWorld && restoredStampRefs.length) {
    world.appendChild(fragment);
    const viewportBounds = getViewportWorldBounds();
    for (const stamp of restoredStampRefs) {
      updateStampViewportVisibility(stamp, viewportBounds);
    }
    scheduleStampVisibilityRefresh();
  }
  return restored;
}

async function restoreSessionState(rawSnapshot = null) {
  let raw = typeof rawSnapshot === "string" ? rawSnapshot : getSessionStorageItemSafe(SESSION_STORAGE_KEY);
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
        originalUrl: typeof brush.originalUrl === "string" && brush.originalUrl
          ? brush.originalUrl
          : brush.url,
        originalWidth: Math.max(1, Number(brush.originalWidth) || Number(brush.width) || 1),
        originalHeight: Math.max(1, Number(brush.originalHeight) || Number(brush.height) || 1),
        frameCount:
          normalizeBrushFrameCount(brush.frameCount) ||
          (getBrushSourceIsGif(brush) ? null : 1),
        frameRange: brush.frameRange && Number.isFinite(Number(brush.frameRange.end))
          ? {
              start: Math.max(0, Math.floor(Number(brush.frameRange.start) || 0)),
              end: Math.max(1, Math.floor(Number(brush.frameRange.end) || 1))
            }
          : null,
        cropRect:
          brush.cropRect &&
          Number.isFinite(Number(brush.cropRect.width)) &&
          Number.isFinite(Number(brush.cropRect.height))
            ? {
                x: Number(brush.cropRect.x) || 0,
                y: Number(brush.cropRect.y) || 0,
                width: Math.max(1, Number(brush.cropRect.width)),
                height: Math.max(1, Number(brush.cropRect.height))
              }
            : null,
        enabled: brush.enabled !== false,
        weightMode: normalizeBrushWeightMode(brush.weightMode)
      }));
    clearBrushFrameCountJobs();

    const snapshotSoloBrushId = Number(snapshot.soloBrushId);
    state.soloBrushId = Number.isFinite(snapshotSoloBrushId) ? snapshotSoloBrushId : null;
    const restoredSelectedBrushIds = Array.isArray(snapshot.selectedBrushIds)
      ? snapshot.selectedBrushIds
      : [];
    const existingBrushIds = new Set(state.brushes.map((brush) => brush.id));
    state.selectedBrushIds = new Set(
      restoredSelectedBrushIds
        .map((id) => Number(id))
        .filter((id) => Number.isFinite(id) && existingBrushIds.has(id))
    );
    if (state.selectedBrushIds.size) {
      state.soloBrushId = null;
      for (const brush of state.brushes) {
        if (state.selectedBrushIds.has(brush.id)) {
          brush.enabled = true;
        }
      }
    }
    const snapshotStockFolderId =
      typeof snapshot.activeStockBrushFolderId === "string"
        ? snapshot.activeStockBrushFolderId
        : "";
	    state.activeStockBrushFolderId = STOCK_BRUSH_FOLDERS.some(
	      (folder) => folder.id === snapshotStockFolderId
	    ) || snapshotStockFolderId === "all" || snapshotStockFolderId === "favorites"
	      ? snapshotStockFolderId
	      : null;
    clearActiveCustomBrushPreset();
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
    if (exportBgImageLayer) {
      world.appendChild(exportBgImageLayer);
    }
    clearStampSpatialIndex();
    state.stampCount = 0;
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

    const controls = snapshot.controls || {};
    const fallbackStrokeTint = normalizeTintSettings({
      color: controls.tintColor,
      amountPercent: controls.tintAmount
    });

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

    state.strokes = restoreStrokeList(snapshot.strokes, brushById, true, fallbackStrokeTint);
    const restoredRedoStrokes = restoreStrokeList(
      snapshot.redoStrokes,
      brushById,
      false,
      fallbackStrokeTint
    );
    for (const stroke of state.strokes) {
      state.strokeById.set(stroke.id, stroke);
    }
    for (const stroke of state.strokes) {
      if (stroke.animationPaused) {
        applyStrokeAnimationPaused(stroke);
      }
    }
    state.history = state.strokes.map((stroke) => ({ type: "draw", stroke }));
    state.redoHistory = restoredRedoStrokes.map((stroke) => ({ type: "draw", stroke }));

    setInputNumericValue(sizeSlider, controls.size);
    consistentToggle.checked = Boolean(controls.consistent);
    setInputNumericValue(consistentSizeSlider, controls.consistentSize);
    setInputNumericValue(spacingSlider, mapSpacingValueToSlider(controls.spacing));
    setInputNumericValue(rotationSlider, controls.rotation);
    setInputNumericValue(opacitySlider, controls.opacity);
    tintColorInput.value = normalizeHexColor(controls.tintColor, "#ffffff");
    setInputNumericValue(tintAmountSlider, controls.tintAmount);
    renderModeToggle.checked = Boolean(controls.renderLinear);
    state.brushPreviewEnabled = controls.brushPreviewEnabled !== false;
    cursorTrailToggle.checked = Boolean(controls.cursorTrailEnabled);
    setInputNumericValue(cursorTrailCountSlider, controls.cursorTrailCount);
    state.drawMode = DRAW_MODES.includes(controls.drawMode) ? controls.drawMode : "pencil";
    setInputNumericValue(spraySpreadSlider, controls.spraySpread ?? DEFAULT_SPRAY_SPREAD);
    state.sidebarCollapsed = Boolean(controls.sidebarCollapsed);
    state.sidebarTab = normalizeSidebarTab(controls.sidebarTab) === "export"
      ? "draw"
      : normalizeSidebarTab(controls.sidebarTab);
    if (Array.isArray(controls.customBrushPresetSources)) {
      state.customBrushPresetSources = normalizeCustomBrushPresetSourcesSnapshot(
        controls.customBrushPresetSources
      );
      saveCustomBrushPresetSources();
    }
    state.activeCustomBrushPresetIndex =
      state.activeStockBrushFolderId === null
        ? normalizeCustomBrushPresetIndex(controls.activeCustomBrushPresetIndex)
        : null;
    state.exportMode = false;
    state.exportSelectionBounds = null;
    state.exportDrag = null;
    state.exportTask = null;
    state.brushGalleryCollapsed = Boolean(controls.brushGalleryCollapsed);
    state.brushGallerySort = normalizeBrushGallerySort(controls.brushGallerySort);
    state.exportBackgroundEnabled = controls.exportBackgroundEnabled !== false;
    state.exportSeeBeyondEnabled = controls.exportSeeBeyondEnabled !== false;
    revokeExportBackgroundImageUrl();
    state.exportBgImageUrl = typeof controls.exportBgImageUrl === "string" &&
      controls.exportBgImageUrl.startsWith("data:image/")
      ? controls.exportBgImageUrl
      : "";
    state.exportBgImagePreviewUrl = isGifUrl(state.exportBgImageUrl) ? "" : state.exportBgImageUrl;
    state.exportBgImageOpacity = clamp(Number(controls.exportBgImageOpacity) || 100, 0, 100);
    state.exportBgImageMode = controls.exportBgImageMode === "tile" ? "tile" : "stretch";
    state.exportBgImageTileSize = normalizeExportBgTileSize(controls.exportBgImageTileSize);
    state.exportBgImageNaturalWidth = Math.max(0, Number(controls.exportBgImageNaturalWidth) || 0);
    state.exportBgImageNaturalHeight = Math.max(0, Number(controls.exportBgImageNaturalHeight) || 0);
    state.lastExportSetup = normalizeExportSetupSnapshot(controls.lastExportSetup);
    state.exportAnimationAuto = controls.exportAnimationAuto !== false;
    state.exportAnimationSeconds = EXPORT_MANUAL_SECONDS_PRESETS.includes(Number(controls.exportAnimationSeconds))
      ? Number(controls.exportAnimationSeconds)
      : 3;
    const restoredFrameCount = String(controls.exportAnimationFrameCount || "").trim();
    state.exportAnimationFrameCount = restoredFrameCount
      ? String(clamp(Math.floor(Number(restoredFrameCount)) || 1, 1, EXPORT_MAX_FRAME_COUNT))
      : "";
    state.exportVideoAuto = controls.exportVideoAuto !== false;
    state.exportVideoSeconds = Number.isFinite(Number(controls.exportVideoSeconds))
      ? clamp(Number(controls.exportVideoSeconds), 0, EXPORT_VIDEO_MAX_SECONDS)
      : 3;
    state.showGifCountIndicator = controls.showGifCountIndicator !== false;
    state.showGifPauseButton = controls.showGifPauseButton !== false;
    state.showDrawBackgroundColorControl = Boolean(controls.showDrawBackgroundColorControl);
    state.canvasBackgroundColor = normalizeHexColor(controls.canvasBackgroundColor, "#ffffff");
    applyCollapsedSliderGroupSnapshot(controls.collapsedSliderGroups);

    updateSliderText();
    updateTintControlUI();
    updateBrushTintMatrix();
    setTintPopoverOpen(false);
    updateConsistentModeUI();
    updateRenderModeUI();
    updateCursorTrailUI();
    updateDrawModeUI();
    updateGifPauseButtonUI();
    updateRotationIndicator();
    updateSidebarVisibilityUI();
    updateSidebarTabUI();
    updateSettingsPanelUI();
    applyCanvasBackgroundColor(state.canvasBackgroundColor);
    updateEraseModeUI();
    updateUndoState();
    updateBrushStatus();
    renderBrushGallery();
    renderStockBrushButtons();
    refreshBrushTintOnVisibleElements();
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
  const hasStamps = getVisibleStampCount() > 0;
  const isBusy = Boolean(state.placementTask || state.exportTask);
  const controlsLocked = state.exportMode || isBusy;

  undoButton.disabled = controlsLocked || !hasHistory;
  redoButton.disabled = controlsLocked || !hasRedo;
  clearButton.disabled = controlsLocked || !hasStamps;
  exportModeButton.disabled = isBusy || !hasStamps;
  exportButton.disabled = !state.exportMode || Boolean(state.exportTask);
  exportCancelButton.disabled = !state.exportTask;
  if (exportVideoButton) {
    exportVideoButton.disabled = !state.exportMode || Boolean(state.exportTask);
  }
  if (exportVideoCancelButton) {
    exportVideoCancelButton.disabled = !state.exportTask;
  }
  updateGifCountIndicator();
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
  const selectedBrushes = getSelectedBrushes();
  if (soloBrush) {
    brushStatus.textContent =
      `Loaded ${state.brushes.length} brush image(s). Solo: ${soloBrush.name}.`;
    return;
  }

  if (selectedBrushes.length) {
    brushStatus.textContent =
      `Loaded ${state.brushes.length} brush image(s). Selected: ${selectedBrushes.length}.`;
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

function getStockBrushFiles(folder) {
  if (!folder || !Array.isArray(folder.files)) {
    return [];
  }
  return folder.files.filter((filePath) =>
    typeof filePath === "string" && ALLOWED_EXTENSIONS.test(filePath)
  );
}

function getStockBrushFolderById(folderId) {
  return STOCK_BRUSH_FOLDERS.find((folder) => folder && folder.id === folderId) || null;
}

function getActiveBrushCategoryName() {
  if (state.activeStockBrushFolderId === "all") {
    return "all";
  }
  if (state.activeStockBrushFolderId === "favorites") {
    return "favorites";
  }
  if (normalizeCustomBrushPresetIndex(state.activeCustomBrushPresetIndex) !== null) {
    return `preset ${state.activeCustomBrushPresetIndex + 1}`;
  }

  const folder = getStockBrushFolderById(state.activeStockBrushFolderId);
  if (folder && typeof folder.name === "string" && folder.name.trim()) {
    return folder.name.trim();
  }

  return "custom";
}

function getOrderedStockBrushFolders() {
  const foldersByName = new Map(
    STOCK_BRUSH_FOLDERS.map((folder) => [String(folder?.name || ""), folder])
  );
  const orderedFolders = [];
  for (const folderName of STOCK_BRUSH_FOLDER_ORDER) {
    const folder = foldersByName.get(folderName);
    if (folder) {
      orderedFolders.push(folder);
      foldersByName.delete(folderName);
    }
  }
  orderedFolders.push(...foldersByName.values());
  return orderedFolders;
}

function encodeStockBrushPath(filePath) {
  return String(filePath)
    .split("/")
    .map((segment) => encodeURIComponent(segment))
    .join("/");
}

function getStockBrushFileName(filePath) {
  const parts = String(filePath).split("/");
  return parts[parts.length - 1] || "brush";
}

function getStockBrushIconPath(folder) {
  if (!folder || !folder.id) {
    return "";
  }
  const cachedPath = stockBrushIconPaths.get(folder.id);
  if (cachedPath) {
    return cachedPath;
  }
  const files = getStockBrushFiles(folder);
  if (!files.length) {
    return "";
  }
  const iconPath = files[Math.floor(Math.random() * files.length)];
  stockBrushIconPaths.set(folder.id, iconPath);
  return iconPath;
}

function renderStockBrushButtons() {
  if (!stockBrushButtons) {
    return;
  }

  const folders = getOrderedStockBrushFolders().filter((folder) => getStockBrushFiles(folder).length);
  const showBrushData = !state.brushGalleryCollapsed;
  stockBrushButtons.hidden = !showBrushData || folders.length === 0;
  stockBrushButtons.innerHTML = "";
  if (loadAllStockBrushesButton) {
    loadAllStockBrushesButton.hidden = !showBrushData || folders.length === 0;
    loadAllStockBrushesButton.disabled = Boolean(state.stockBrushLoadingFolderId) || folders.length === 0;
    loadAllStockBrushesButton.classList.toggle("is-active", state.activeStockBrushFolderId === "all");
    loadAllStockBrushesButton.classList.toggle("is-loading", state.stockBrushLoadingFolderId === "all");
  }
  updateFavoriteBrushButtons();
  if (!showBrushData || !folders.length) {
    return;
  }

  const fragment = document.createDocumentFragment();
  for (const folder of folders) {
    const button = document.createElement("button");
    const iconPath = getStockBrushIconPath(folder);
    const isActive = state.activeStockBrushFolderId === folder.id;
    const isLoading = state.stockBrushLoadingFolderId === folder.id;
    button.type = "button";
    button.className = "stock-brush-button";
    button.dataset.stockBrushFolderId = folder.id;
    button.title = `Load ${folder.name} stock brushes`;
    button.setAttribute("aria-label", `Load ${folder.name} stock brushes`);
    button.setAttribute("aria-pressed", isActive ? "true" : "false");
    button.disabled = Boolean(state.stockBrushLoadingFolderId);
    button.classList.toggle("is-active", isActive);
    button.classList.toggle("is-loading", isLoading);

    if (iconPath) {
      const icon = document.createElement("img");
      icon.className = "stock-brush-icon";
      icon.src = encodeStockBrushPath(iconPath);
      icon.alt = "";
      icon.draggable = false;
      icon.loading = "lazy";
      icon.decoding = "async";
      applyGifPauseStateToImage(icon);
      button.appendChild(icon);
    }

    fragment.appendChild(button);
  }

  stockBrushButtons.appendChild(fragment);
}

function getSortedBrushGalleryBrushes() {
  const sortMode = normalizeBrushGallerySort(state.brushGallerySort);
  const brushes = state.brushes.slice();
  const byName = (a, b) => String(a.name || "").localeCompare(String(b.name || ""), undefined, {
    numeric: true,
    sensitivity: "base"
  });

  if (sortMode === "area-asc" || sortMode === "area-desc") {
    brushes.sort((a, b) => {
      const areaA = Math.max(1, Number(a.width) || 1) * Math.max(1, Number(a.height) || 1);
      const areaB = Math.max(1, Number(b.width) || 1) * Math.max(1, Number(b.height) || 1);
      const delta = sortMode === "area-asc" ? areaA - areaB : areaB - areaA;
      return delta || byName(a, b);
    });
    return brushes;
  }

  brushes.sort(byName);
  return brushes;
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
  updateBrushDataToggleUI();
  brushGallery.innerHTML = "";
  const showBrushFileMeta = state.sidebarTab === "brushes";
  const activePresetIndex = normalizeCustomBrushPresetIndex(state.activeCustomBrushPresetIndex);
  if (brushSortSelect) {
    brushSortSelect.value = normalizeBrushGallerySort(state.brushGallerySort);
  }

  const showBrushData = !state.brushGalleryCollapsed;
  dropZone.hidden = !showBrushData;
  dropZone.style.display = showBrushData ? "" : "none";
  dropZonePrompt.hidden = !showBrushData;
  unloadBrushDataButton.hidden = !showBrushData;
  if (brushSortControls) {
    brushSortControls.hidden = !showBrushData;
  }
  if (!showBrushData) {
    dropZone.classList.remove("has-gallery");
    dropZoneHeader.classList.add("no-unload");
    brushGallery.hidden = true;
    return;
  }

  const hasBrushes = state.brushes.length > 0;
  unloadBrushDataButton.hidden = !hasBrushes;
  unloadBrushDataButton.disabled = !hasBrushes;
  dropZoneHeader.classList.toggle("no-unload", !hasBrushes);
  const showGallery = hasBrushes;
  dropZone.classList.toggle("has-gallery", hasBrushes);
  brushGallery.hidden = !showGallery;

  if (!showGallery) {
    return;
  }

  const fragment = document.createDocumentFragment();
  const soloBrush = getSoloBrush();
  const selectedBrushes = getSelectedBrushes();
  const selectedBrushIds = new Set(selectedBrushes.map((brush) => brush.id));
  for (const brush of getSortedBrushGalleryBrushes()) {
    const card = document.createElement("div");
    card.className = "brush-item";
    const isSolo = soloBrush && soloBrush.id === brush.id;
    const isSelected = selectedBrushIds.has(brush.id);
    if (!brush.enabled) {
      card.classList.add("is-disabled");
    }
    if (isSolo) {
      card.classList.add("is-solo");
    } else if (isSelected) {
      card.classList.add("is-selected");
    } else if (soloBrush || selectedBrushIds.size) {
      card.classList.add("is-solo-muted");
    }
    card.dataset.brushId = String(brush.id);
    card.draggable = true;

    const preview = document.createElement("img");
    preview.className = "brush-thumb";
    preview.src = brush.url;
    preview.alt = brush.name;
    preview.draggable = true;
    preview.loading = "lazy";
    preview.decoding = "async";
    applyBrushGalleryPreviewAnimationState(preview, brush);
    applyBrushTintStyle(preview, !brush.enabled, NO_TINT_SETTINGS);

    const drawingFavoriteButton = document.createElement("button");
    drawingFavoriteButton.type = "button";
    drawingFavoriteButton.className = "brush-favorite-overlay-button";
    drawingFavoriteButton.dataset.action = "favorite";
    drawingFavoriteButton.textContent = isBrushFavorite(brush) ? "★" : "☆";
    drawingFavoriteButton.title = isBrushFavorite(brush) ? "Remove from favorites" : "Add to favorites";
    drawingFavoriteButton.setAttribute("aria-label", drawingFavoriteButton.title);
    drawingFavoriteButton.setAttribute("aria-pressed", isBrushFavorite(brush) ? "true" : "false");
    drawingFavoriteButton.classList.toggle("is-active", isBrushFavorite(brush));

    let presetRemoveButton = null;
    if (activePresetIndex !== null && isActiveCustomBrushPresetSource(getBrushPresetSource(brush))) {
      presetRemoveButton = document.createElement("button");
      presetRemoveButton.type = "button";
      presetRemoveButton.className = "brush-preset-remove-button";
      presetRemoveButton.dataset.action = "remove-preset";
      presetRemoveButton.textContent = "x";
      presetRemoveButton.title = "Remove from custom brush preset";
      presetRemoveButton.setAttribute("aria-label", "Remove from custom brush preset");
    }

    const name = document.createElement("p");
    name.className = "brush-name";
    name.textContent = brush.name;

    let meta = null;
    if (showBrushFileMeta) {
      ensureBrushFrameCount(brush);
      meta = document.createElement("p");
      meta.className = "brush-meta";
      meta.textContent = getBrushMetaText(brush);
    }

    const actionRow = document.createElement("div");
    actionRow.className = "brush-actions";

    const enabledButton = createBrushActionButton(
      "toggle-enabled",
      "👁",
      brush.enabled,
      brush.enabled
        ? "Disable brush image"
        : "Enable brush image"
    );
    if (isSolo) {
      enabledButton.classList.add("is-solo");
      enabledButton.title = "Solo brush active";
      enabledButton.setAttribute("aria-label", "Solo brush active");
    }
    const cropButton = createBrushActionButton(
      "crop",
      "",
      false,
      "Open source editor"
    );
    const favoriteButton = createBrushActionButton(
      "favorite",
      isBrushFavorite(brush) ? "★" : "☆",
      isBrushFavorite(brush),
      isBrushFavorite(brush) ? "Remove from favorites" : "Add to favorites"
    );

    actionRow.appendChild(enabledButton);
    actionRow.appendChild(cropButton);
    actionRow.appendChild(favoriteButton);
    card.appendChild(preview);
    card.appendChild(drawingFavoriteButton);
    if (presetRemoveButton) {
      card.appendChild(presetRemoveButton);
    }
    card.appendChild(name);
    if (meta) {
      card.appendChild(meta);
    }
    card.appendChild(actionRow);
    fragment.appendChild(card);
  }

  brushGallery.appendChild(fragment);
}

function getStrokeLayerName(stroke) {
  const stampCount = Array.isArray(stroke?.elements) ? stroke.elements.length : 0;
  const categoryName = typeof stroke?.brushCategoryName === "string" && stroke.brushCategoryName.trim()
    ? stroke.brushCategoryName.trim()
    : "custom";
  const layerType = normalizeStrokeLayerType(stroke?.layerType);
  const typeLabel = layerType;
  const layerNumber = Number.isFinite(Number(stroke?.layerNumber))
    ? Number(stroke.layerNumber)
    : Number.isFinite(Number(stroke?.id))
    ? Number(stroke.id)
    : 1;
  return `${categoryName} ${typeLabel} ${layerNumber} (${stampCount})`;
}

function selectEditLayer(strokeId) {
  const numericId = Number(strokeId);
  state.selectedEditLayerId = Number.isFinite(numericId) ? numericId : null;
  renderEditLayers();
}

function createEditLayerPreview(stroke) {
  const canvas = document.createElement("canvas");
  canvas.className = "edit-layer-preview";
  canvas.width = 64;
  canvas.height = 64;
  canvas.setAttribute("aria-hidden", "true");
  if (!stroke || !Array.isArray(stroke.elements) || !stroke.elements.length) {
    return canvas;
  }

  const boundsList = stroke.elements.map((element) => getCachedStampWorldBounds(element));
  const left = Math.min(...boundsList.map((bounds) => bounds.left));
  const top = Math.min(...boundsList.map((bounds) => bounds.top));
  const right = Math.max(...boundsList.map((bounds) => bounds.right));
  const bottom = Math.max(...boundsList.map((bounds) => bounds.bottom));
  const width = Math.max(1, right - left);
  const height = Math.max(1, bottom - top);
  const scale = Math.min(60 / width, 60 / height);
  const offsetX = (64 - width * scale) / 2;
  const offsetY = (64 - height * scale) / 2;
  const ctx = canvas.getContext("2d", { alpha: true });
  if (!ctx) {
    return canvas;
  }

  ctx.imageSmoothingEnabled = false;
  const maxPreviewStamps = 32;
  const step = Math.max(1, Math.ceil(stroke.elements.length / maxPreviewStamps));
  for (let index = 0; index < stroke.elements.length; index += step) {
    const element = stroke.elements[index];
    if (!(element instanceof HTMLImageElement) || !element.complete || element.naturalWidth <= 0) {
      continue;
    }
    const elementLeft = parseFloat(element.style.left) || 0;
    const elementTop = parseFloat(element.style.top) || 0;
    const elementWidth = Math.max(1, parseFloat(element.style.width) || 1);
    const elementHeight = Math.max(1, parseFloat(element.style.height) || 1);
    try {
      ctx.globalAlpha = clamp(Number(element.dataset.sequenceBaseOpacity || element.style.opacity) || 1, 0, 1);
      ctx.drawImage(
        element,
        offsetX + (elementLeft - left) * scale,
        offsetY + (elementTop - top) * scale,
        Math.max(1, elementWidth * scale),
        Math.max(1, elementHeight * scale)
      );
    } catch (error) {
      // Cross-origin or not-yet-ready images simply skip the lightweight preview.
    }
  }
  ctx.globalAlpha = 1;
  return canvas;
}

function applyStrokeVisibility(stroke) {
  if (!stroke || !Array.isArray(stroke.elements)) {
    return;
  }

  const hidden = Boolean(stroke.hidden);
  resetStrokeSequenceRuntime(stroke);
  const viewportBounds = getViewportWorldBounds();
  for (const element of stroke.elements) {
    resetStampSequenceStyle(element);
    element.classList.toggle("is-layer-hidden", hidden);
    if (hidden) {
      unregisterStampSpatialCells(element);
    } else if (element.parentElement === world) {
      registerStampSpatialCells(element);
      updateStampViewportVisibility(element, viewportBounds);
    }
  }
  updateUndoState();
  scheduleStampVisibilityRefresh();
}

function applyStrokeAnimationPaused(stroke) {
  if (!stroke || !Array.isArray(stroke.elements)) {
    return;
  }

  const elements = stroke.elements.filter((element) => element instanceof HTMLImageElement);
  window.requestAnimationFrame(() => {
    for (const element of elements) {
      if (stroke.animationPaused) {
        freezeGifImage(element);
      } else if (!state.gifAnimationsPaused) {
        resumeGifImage(element);
      }
    }
    scheduleStampVisibilityRefresh();
  });
}

function applyGlobalGifPauseState(paused) {
  const shouldPause = Boolean(paused);
  const images = Array.from(document.querySelectorAll("img"));
  if (shouldPause) {
    for (const image of images) {
      freezeGifImage(image);
    }
    scheduleStampVisibilityRefresh();
    return;
  }

  let index = 0;

  function processBatch() {
    const batchEnd = Math.min(images.length, index + 80);
    for (; index < batchEnd; index += 1) {
      const image = images[index];
      if (shouldPause) {
        freezeGifImage(image);
      } else if (!isImageLayerPaused(image)) {
        resumeGifImage(image);
      }
    }

    if (index < images.length) {
      window.requestAnimationFrame(processBatch);
      return;
    }

    scheduleStampVisibilityRefresh();
  }

  window.requestAnimationFrame(processBatch);
}

function getSequenceEffectDuration(effect, settings) {
  if (effect === "image-cycle") {
    return getImageCycleDurationMs(settings);
  }
  if (effect === "move") {
    return getMoveDurationMs(settings);
  }
  if (effect === "rotate") {
    return getRotateDurationMs(settings);
  }
  if (effect === "scale") {
    return getScaleDurationMs(settings);
  }
  if (effect === "color-cycle") {
    return settings.colorCycleInstant ? 1 : getColorCycleDurationMs(settings);
  }
  if (effect === "show-hide") {
    return Math.max(100, settings.showHideFadeLength * 2 || 500);
  }
  return 500;
}

function mapSequenceSlider(value, lowValue, highValue) {
  const percent = (clamp(Number(value) || 1, 1, 100) - 1) / 99;
  return lowValue + (highValue - lowValue) * percent;
}

function mapExponentialSequenceSlider(value, min, max, lowValue, highValue) {
  const percent = (clamp(Number(value) || min, min, max) - min) / (max - min);
  return lowValue * Math.pow(highValue / lowValue, percent);
}

function mapCompressedSequenceSlider(key, value, lowValue, highValue) {
  const percent = (mapSequenceSettingToSliderPosition(key, value) - 1) / 99;
  return lowValue + (highValue - lowValue) * percent;
}

function normalizeSequenceSpeedSliderValue(value, slowValue, fastValue, fallback = 50) {
  const numericValue = Number(value);
  if (!Number.isFinite(numericValue)) {
    return fallback;
  }
  if (numericValue >= 1 && numericValue <= 100) {
    return Math.round(numericValue);
  }
  const percent = (clamp(numericValue, fastValue, slowValue) - slowValue) / (fastValue - slowValue);
  return clamp(Math.round(1 + percent * 99), 1, 100);
}

function getRotateDurationMs(settings) {
  return mapExponentialSequenceSlider(settings.rotateSpeed, 1, 100, 90000, 60);
}

function getScaleDurationMs(settings) {
  return mapSequenceSlider(settings.scaleSpeed, 6000, 100);
}

function getMoveDurationMs(settings) {
  return mapSequenceSlider(settings.moveSpeed, 4000, 50);
}

function getColorCycleDurationMs(settings) {
  return mapSequenceSlider(settings.colorCycleSpeed, 5000, 50);
}

function getImageCycleDurationMs(settings) {
  return mapCompressedSequenceSlider("imageCycleSpeed", settings.imageCycleSpeed, 4000, 50);
}

function getPulseSpacingMs(settings) {
  return mapCompressedSequenceSlider("pulseSpeed", settings.pulseSpeed, 700, 15);
}

function getPulseIntervalMs(settings) {
  return mapCompressedSequenceSlider("pulseRate", settings.pulseRate, 5000, 100);
}

function getWaveSpacingMs(settings) {
  return mapSequenceSlider(settings.waveSpeed, 2000, 20);
}

function getRandomIntervalMs(settings) {
  return mapSequenceSlider(settings.randomSpeed, 4000, 50);
}

function resetStrokeSequenceRuntime(stroke) {
  if (!stroke) {
    return;
  }
  stroke.sequenceRuntime = null;
  stroke.sequenceSlotRuntimes = null;
  delete stroke.sequencePauseStartTime;
}

function refreshStrokeSequenceEffect(stroke) {
  if (!stroke) {
    return;
  }
  resetStrokeSequenceRuntime(stroke);
  for (const stamp of stroke.elements || []) {
    resetStampSequenceStyle(stamp, true);
  }
}

function sequenceHash(seed, index) {
  let value = (Math.imul(seed + 1, 1103515245) + Math.imul(index + 17, 12345)) >>> 0;
  value ^= value >>> 16;
  value = Math.imul(value, 2246822507) >>> 0;
  value ^= value >>> 13;
  return (value >>> 0) / 4294967295;
}

function sequenceKeyNumber(key) {
  const text = String(key || "");
  let hash = 0;
  for (let index = 0; index < text.length; index += 1) {
    hash = (Math.imul(hash, 31) + text.charCodeAt(index)) >>> 0;
  }
  return hash;
}

function getSequenceRuntimeBaseTime(runtime, now) {
  const baseTime = Number(runtime?.baseTime);
  return Number.isFinite(baseTime) ? baseTime : now;
}

function getLayerSequenceTrigger(stroke, index, total, style, settings, now, effectDuration, runtimeHost = stroke) {
  const safeTotal = Math.max(1, total);
  if (style === "pulse") {
    if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== "pulse") {
      runtimeHost.sequenceRuntime = {
        style: "pulse",
        pulseBaseTime: now,
        triggeredPulseByIndex: [],
        lastTriggeredIndexByPulse: new Map(),
        frameTime: 0,
        triggeredPulseIdsThisFrame: new Set()
      };
    }
    const runtime = runtimeHost.sequenceRuntime;
    if (!Array.isArray(runtime.triggeredPulseByIndex)) {
      runtime.triggeredPulseByIndex = [];
    }
    if (!(runtime.lastTriggeredIndexByPulse instanceof Map)) {
      runtime.lastTriggeredIndexByPulse = new Map();
    }
    if (runtime.frameTime !== now) {
      runtime.frameTime = now;
      runtime.triggeredPulseIdsThisFrame = new Set();
    }
    const spacing = getPulseSpacingMs(settings);
    const interval = Math.max(16, getPulseIntervalMs(settings));
    const maxDuePulseId = Math.floor((now - runtime.pulseBaseTime - index * spacing) / interval);
    const lastPulseForIndex = Number.isFinite(Number(runtime.triggeredPulseByIndex[index]))
      ? Number(runtime.triggeredPulseByIndex[index])
      : -1;
    const pulseId = lastPulseForIndex + 1;
    const previousIndex = index <= 0
      ? index - 1
      : Number(runtime.lastTriggeredIndexByPulse.get(pulseId));

    if (
      maxDuePulseId < pulseId ||
      previousIndex < index - 1 ||
      runtime.triggeredPulseIdsThisFrame.has(pulseId)
    ) {
      return { active: false, key: "", startTime: 0, endTime: 0 };
    }

    runtime.triggeredPulseByIndex[index] = pulseId;
    runtime.lastTriggeredIndexByPulse.set(pulseId, index);
    runtime.triggeredPulseIdsThisFrame.add(pulseId);

    const stalePulseThreshold = pulseId - Math.max(12, safeTotal * 2);
    for (const [storedPulseId] of runtime.lastTriggeredIndexByPulse) {
      if (storedPulseId < stalePulseThreshold) {
        runtime.lastTriggeredIndexByPulse.delete(storedPulseId);
      }
    }

    return {
      active: true,
      key: `${style}:${pulseId}:${index}`,
      startTime: now,
      endTime: now + Math.max(16, effectDuration)
    };
  }

  if (runtimeHost.sequenceRuntime && runtimeHost.sequenceRuntime.style !== style) {
    resetStrokeSequenceRuntime(runtimeHost);
  }

  if (style === "all") {
    if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== "all") {
      runtimeHost.sequenceRuntime = {
        style: "all",
        baseTime: now
      };
    }
    const runtime = runtimeHost.sequenceRuntime;
    const interval = Math.max(100, effectDuration);
    const baseTime = getSequenceRuntimeBaseTime(runtime, now);
    const elapsed = Math.max(0, now - baseTime);
    const tick = Math.floor(elapsed / interval);
    const startTime = baseTime + tick * interval;
    return {
      active: true,
      key: `${style}:${tick}`,
      startTime,
      endTime: startTime + interval
    };
  }

  if (style === "wave") {
    if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== "wave") {
      const initialIndex = settings.waveReverse ? safeTotal - 1 : 0;
      runtimeHost.sequenceRuntime = {
        style: "wave",
        bounceId: 0,
        initialIndex,
        nextIndex: initialIndex,
        direction: settings.waveReverse ? -1 : 1,
        repeatEndpointIndex: null,
        hasLeftInitialEndpoint: false,
        nextTriggerTime: now,
        frameTime: 0,
        triggeredThisFrame: false
      };
    }
    const runtime = runtimeHost.sequenceRuntime;
    if (runtime.frameTime !== now) {
      runtime.frameTime = now;
      runtime.triggeredThisFrame = false;
    }
    const spacing = getWaveSpacingMs(settings);
    if (runtime.triggeredThisFrame || now < runtime.nextTriggerTime || index !== runtime.nextIndex) {
      return { active: false, key: "", startTime: 0, endTime: 0 };
    }

    const triggerIndex = runtime.nextIndex;
    const bounceId = runtime.bounceId;
    runtime.triggeredThisFrame = true;
    runtime.bounceId += 1;
    if (safeTotal <= 1) {
      runtime.nextIndex = 0;
      runtime.direction = settings.waveReverse ? -1 : 1;
      runtime.repeatEndpointIndex = 0;
      runtime.hasLeftInitialEndpoint = true;
    } else {
      const isEndpoint = triggerIndex <= 0 || triggerIndex >= safeTotal - 1;
      const isInitialEndpoint =
        triggerIndex === runtime.initialIndex && runtime.hasLeftInitialEndpoint !== true;
      if (runtime.repeatEndpointIndex === triggerIndex) {
        runtime.repeatEndpointIndex = null;
        if (triggerIndex <= 0) {
          runtime.direction = 1;
          runtime.nextIndex = 1;
        } else {
          runtime.direction = -1;
          runtime.nextIndex = safeTotal - 2;
        }
      } else if (isEndpoint && !isInitialEndpoint) {
        runtime.repeatEndpointIndex = triggerIndex;
        runtime.nextIndex = triggerIndex;
      } else {
        runtime.hasLeftInitialEndpoint =
          runtime.hasLeftInitialEndpoint || triggerIndex !== runtime.initialIndex;
        let nextIndex = triggerIndex + runtime.direction;
        if (nextIndex >= safeTotal) {
          runtime.direction = -1;
          nextIndex = safeTotal - 1;
        } else if (nextIndex < 0) {
          runtime.direction = 1;
          nextIndex = 0;
        }
        runtime.nextIndex = clamp(nextIndex, 0, safeTotal - 1);
      }
    }
    runtime.nextTriggerTime = now + spacing;
    return {
      active: true,
      key: `${style}:${bounceId}:${triggerIndex}`,
      startTime: now,
      endTime: now + Math.max(16, effectDuration)
    };
  }

  if (style === "step") {
    if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== "step") {
      runtimeHost.sequenceRuntime = {
        style: "step",
        baseTime: now
      };
    }
    const runtime = runtimeHost.sequenceRuntime;
    const stepLength = Math.max(50, settings.stepLength);
    const stepAmount = Math.max(1, Math.round(settings.stepAmount));
    const baseTime = getSequenceRuntimeBaseTime(runtime, now);
    const elapsed = Math.max(0, now - baseTime);
    const tick = Math.floor(elapsed / stepLength);
    const start = (tick * stepAmount) % safeTotal;
    const offset = (index - start + safeTotal) % safeTotal;
    const active = offset < Math.min(stepAmount, safeTotal);
    const startTime = baseTime + tick * stepLength;
    return {
      active,
      key: `${style}:${tick}`,
      startTime,
      endTime: startTime + stepLength
    };
  }

  if (style === "random") {
    if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== "random") {
      runtimeHost.sequenceRuntime = {
        style: "random",
        baseTime: now
      };
    }
    const runtime = runtimeHost.sequenceRuntime;
    const speed = getRandomIntervalMs(settings);
    const baseTime = getSequenceRuntimeBaseTime(runtime, now);
    const elapsed = Math.max(0, now - baseTime);
    const tick = Math.floor(elapsed / speed);
    const active = sequenceHash(tick, index) > 0.68;
    const startTime = baseTime + tick * speed;
    return {
      active,
      key: `${style}:${tick}`,
      startTime,
      endTime: startTime + speed
    };
  }

  return { active: false, key: "", startTime: 0, endTime: 0 };
}

function getSequenceBrushPool() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    return [soloBrush];
  }
  const selectedBrushes = getSelectedBrushes();
  const candidates = selectedBrushes.length
    ? selectedBrushes
    : state.brushes.filter((brush) => brush.enabled);
  return candidates.filter((brush) => brush && brush.url);
}

function ensureStampSequenceBase(stamp) {
  if (!stamp.dataset.sequenceBaseOpacity) {
    stamp.dataset.sequenceBaseOpacity = String(
      Number.isFinite(Number(stamp.style.opacity)) ? clamp(Number(stamp.style.opacity), 0, 1) : 1
    );
  }
  if (!stamp.dataset.sequenceBaseSrc) {
    stamp.dataset.sequenceBaseSrc = stamp.dataset.brushUrl || stamp.getAttribute("src") || "";
  }
}

function getStampBaseTintSettings(stamp) {
  return normalizeTintSettings({
    color: stamp?.dataset?.tintColor || "#ffffff",
    amountPercent: Number(stamp?.dataset?.tintAmount) || 0
  });
}

function setStampSequenceImage(stamp, src) {
  if (!src || stamp.getAttribute("src") === src) {
    return;
  }
  stamp.src = src;
  markGifPlaybackStart(stamp, src);
  if (!state.sequenceExportActive) {
    applyGifPauseStateToImage(stamp);
  }
}

function getCurrentSequenceImageSource(stamp, fallbackSrc = "") {
  return stamp?.dataset?.sequenceImageCycleSrc ||
    fallbackSrc ||
    stamp?.dataset?.sequenceBaseSrc ||
    stamp?.dataset?.brushUrl ||
    stamp?.getAttribute("src") ||
    "";
}

function resetStampSequenceStyle(stamp, force = false) {
  if (!stamp || (!force && stamp.dataset.sequenceActive !== "1")) {
    return;
  }
  ensureStampSequenceBase(stamp);
  const baseRotation = Number(stamp.dataset.rotation) || 0;
  stamp.style.transform = `rotate(${baseRotation}deg)`;
  stamp.style.opacity = String(clamp(Number(stamp.dataset.sequenceBaseOpacity) || 1, 0, 1));
  applyBrushTintStyle(stamp, false, getStampBaseTintSettings(stamp));
  setStampSequenceImage(stamp, stamp.dataset.sequenceBaseSrc || stamp.dataset.brushUrl || "");
  deleteSequenceRuntimeDataset(stamp);
}

function triggerImageCycleSequence(stamp, trigger, settings, pool, index, currentSource = "") {
  if (!pool.length) {
    return;
  }
  const currentSrc = currentSource || getCurrentSequenceImageSource(stamp);
  let poolIndex = pool.findIndex((brush) => brush.url === currentSrc);
  if (poolIndex < 0) {
    poolIndex = 0;
  }
  const nextIndex = settings.imageCycleRandom
    ? Math.floor(sequenceHash(sequenceKeyNumber(trigger.key), index + poolIndex) * pool.length) % pool.length
    : (poolIndex + 1) % pool.length;
  const safeNextIndex = pool.length > 1 && pool[nextIndex]?.url === currentSrc
    ? (nextIndex + 1) % pool.length
    : nextIndex;
  stamp.dataset.sequenceImageCycleKey = trigger.key;
  stamp.dataset.sequenceImageCycleSrc = pool[safeNextIndex]?.url || currentSrc;
}

function getCurrentSequenceScale(stamp, settings, now) {
  const startTime = Number(stamp.dataset.sequenceScaleStart);
  const duration = Number.isFinite(Number(stamp.dataset.sequenceScaleDuration))
    ? Math.max(1, Number(stamp.dataset.sequenceScaleDuration))
    : getScaleDurationMs(settings);
  const from = Number(stamp.dataset.sequenceScaleFrom);
  const to = Number(stamp.dataset.sequenceScaleTo);
  if (Number.isFinite(startTime) && Number.isFinite(from) && Number.isFinite(to)) {
    const progress = clamp((now - startTime) / duration, 0, 1);
    const eased = progress < 0.5
      ? 2 * progress * progress
      : 1 - Math.pow(-2 * progress + 2, 2) / 2;
    const scale = from + (to - from) * eased;
    if (progress >= 1) {
      stamp.dataset.sequenceScaleFrom = String(to);
      stamp.dataset.sequenceScaleTo = String(to);
      delete stamp.dataset.sequenceScaleStart;
      delete stamp.dataset.sequenceScaleDuration;
    }
    return scale;
  }
  return Number(stamp.dataset.sequenceScaleTarget) || 1;
}

function getCurrentSequenceMove(stamp, settings, now) {
  if (settings.moveMode === "circle") {
    const strength = Math.max(0, Number(settings.moveStrength) || 0);
    const startTime = Number.isFinite(Number(stamp.dataset.sequenceMoveStart))
      ? Number(stamp.dataset.sequenceMoveStart)
      : now;
    const duration = getMoveDurationMs(settings);
    const phase = ((now - startTime) / Math.max(1, duration)) * Math.PI * 2;
    const offset = Number(stamp.dataset.sequenceMoveCircleStep) || 0;
    return {
      x: Math.cos(phase + offset) * strength,
      y: Math.sin(phase + offset) * strength
    };
  }

  const startTime = Number(stamp.dataset.sequenceMoveStart);
  const duration = Number.isFinite(Number(stamp.dataset.sequenceMoveDuration))
    ? Math.max(1, Number(stamp.dataset.sequenceMoveDuration))
    : getMoveDurationMs(settings);
  const fromX = Number(stamp.dataset.sequenceMoveFromX);
  const fromY = Number(stamp.dataset.sequenceMoveFromY);
  const toX = Number(stamp.dataset.sequenceMoveToX);
  const toY = Number(stamp.dataset.sequenceMoveToY);
  if (
    Number.isFinite(startTime) &&
    Number.isFinite(fromX) &&
    Number.isFinite(fromY) &&
    Number.isFinite(toX) &&
    Number.isFinite(toY)
  ) {
    const progress = clamp((now - startTime) / duration, 0, 1);
    const eased = progress < 0.5
      ? 2 * progress * progress
      : 1 - Math.pow(-2 * progress + 2, 2) / 2;
    const move = {
      x: fromX + (toX - fromX) * eased,
      y: fromY + (toY - fromY) * eased
    };
    if (progress >= 1) {
      stamp.dataset.sequenceMoveFromX = String(toX);
      stamp.dataset.sequenceMoveFromY = String(toY);
      stamp.dataset.sequenceMoveToX = String(toX);
      stamp.dataset.sequenceMoveToY = String(toY);
      delete stamp.dataset.sequenceMoveStart;
      delete stamp.dataset.sequenceMoveDuration;
    }
    return move;
  }
  return {
    x: Number(stamp.dataset.sequenceMoveToX) || 0,
    y: Number(stamp.dataset.sequenceMoveToY) || 0
  };
}

function getSequenceMoveTarget(stamp, trigger, settings, index) {
  const strength = Math.max(0, Number(settings.moveStrength) || 0);
  const mode = settings.moveMode || "left";
  if (mode === "left" || mode === "right" || mode === "up" || mode === "down") {
    const expanded = stamp.dataset.sequenceMoveExpanded !== "1";
    const multiplier = expanded ? 1 : 0;
    return {
      x: mode === "left" ? -strength * multiplier : mode === "right" ? strength * multiplier : 0,
      y: mode === "up" ? -strength * multiplier : mode === "down" ? strength * multiplier : 0,
      expanded
    };
  }
  if (mode === "swing") {
    const currentStep = Number(stamp.dataset.sequenceMoveCircleStep) || 0;
    const nextStep = currentStep + 1;
    const angle = nextStep * (Math.PI / 4) + index * 0.11;
    return {
      x: Math.cos(angle) * strength,
      y: Math.sin(angle) * strength,
      circleStep: nextStep
    };
  }

  const seed = sequenceKeyNumber(trigger?.key) + index * 97;
  const angle = sequenceHash(seed, index) * Math.PI * 2;
  const radius = Math.sqrt(sequenceHash(seed + 13, index + 3)) * strength;
  return {
    x: Math.cos(angle) * radius,
    y: Math.sin(angle) * radius
  };
}

function getCurrentSequenceOpacity(stamp, settings, now) {
  const baseOpacity = clamp(Number(stamp.dataset.sequenceBaseOpacity) || 1, 0, 1);
  const target = Number(stamp.dataset.sequenceVisibilityTo);
  const startTime = Number(stamp.dataset.sequenceVisibilityStart);
  const from = Number(stamp.dataset.sequenceVisibilityFrom);
  const to = Number(stamp.dataset.sequenceVisibilityTo);
  if (!Number.isFinite(startTime) || !Number.isFinite(from) || !Number.isFinite(to)) {
    return Number.isFinite(target) ? target : baseOpacity;
  }
  const duration = Number.isFinite(Number(stamp.dataset.sequenceVisibilityDuration))
    ? Math.max(1, Number(stamp.dataset.sequenceVisibilityDuration))
    : Math.max(1, settings.showHideFade ? settings.showHideFadeLength : 1);
  const progress = clamp((now - startTime) / duration, 0, 1);
  const eased = progress < 0.5
    ? 2 * progress * progress
    : 1 - Math.pow(-2 * progress + 2, 2) / 2;
  if (progress >= 1) {
    delete stamp.dataset.sequenceVisibilityStart;
    delete stamp.dataset.sequenceVisibilityFrom;
    delete stamp.dataset.sequenceVisibilityDuration;
    stamp.dataset.sequenceVisibilityTo = String(to);
    return to;
  }
  return from + (to - from) * eased;
}

function getCurrentSequenceColorAmount(stamp, settings, now) {
  const target = Number(stamp.dataset.sequenceColorTo);
  const startTime = Number(stamp.dataset.sequenceColorStart);
  const from = Number(stamp.dataset.sequenceColorFrom);
  const to = Number(stamp.dataset.sequenceColorTo);
  if (!Number.isFinite(startTime) || !Number.isFinite(from) || !Number.isFinite(to)) {
    return Number.isFinite(target) ? clamp(target, 0, 100) : 0;
  }
  const duration = Number.isFinite(Number(stamp.dataset.sequenceColorDuration))
    ? Math.max(1, Number(stamp.dataset.sequenceColorDuration))
    : getColorCycleDurationMs(settings);
  const progress = clamp((now - startTime) / duration, 0, 1);
  const eased = progress < 0.5
    ? 2 * progress * progress
    : 1 - Math.pow(-2 * progress + 2, 2) / 2;
  if (progress >= 1) {
    stamp.dataset.sequenceColorFrom = String(to);
    stamp.dataset.sequenceColorTo = String(to);
    stamp.dataset.sequenceColorTarget = String(to);
    delete stamp.dataset.sequenceColorStart;
    delete stamp.dataset.sequenceColorDuration;
    return clamp(to, 0, 100);
  }
  return clamp(from + (to - from) * eased, 0, 100);
}

function applySequenceColorStyle(stamp, settings, amountPercent) {
  const amount = clamp(Number(amountPercent) || 0, 0, 100);
  if (amount <= 0) {
    applyBrushTintStyle(stamp, false, getStampBaseTintSettings(stamp));
    return;
  }
  applyBrushTintStyle(
    stamp,
    false,
    createLayeredTintSettings(getStampBaseTintSettings(stamp), {
      color: settings.colorCycleColor,
      amountPercent: amount
    })
  );
}

function getCurrentSequenceRotation(stamp, settings, now) {
  if (settings.rotateContinuous) {
    const restAngle = Number(stamp.dataset.sequenceRotateRestAngle);
    const continuousStart = Number(stamp.dataset.sequenceRotateContinuousStart);
    const active = stamp.dataset.sequenceRotateContinuousActive === "1";
    if (!active) {
      const startTime = Number(stamp.dataset.sequenceRotateStart);
      const from = Number(stamp.dataset.sequenceRotateFrom);
      const to = Number(stamp.dataset.sequenceRotateTo);
      const duration = Number.isFinite(Number(stamp.dataset.sequenceRotateDuration))
        ? Math.max(1, Number(stamp.dataset.sequenceRotateDuration))
        : SEQUENCE_INTERRUPT_TWEEN_MS;
      if (!Number.isFinite(startTime) || !Number.isFinite(from) || !Number.isFinite(to)) {
        return Number.isFinite(restAngle) ? restAngle : 0;
      }
      const progress = clamp((now - startTime) / duration, 0, 1);
      const eased = 1 - Math.pow(1 - progress, 3);
      if (progress >= 1) {
        delete stamp.dataset.sequenceRotateStart;
        delete stamp.dataset.sequenceRotateFrom;
        delete stamp.dataset.sequenceRotateTo;
        delete stamp.dataset.sequenceRotateDuration;
        stamp.dataset.sequenceRotateRestAngle = String(to);
        return to;
      }
      return from + (to - from) * eased;
    }
    if (!Number.isFinite(continuousStart)) {
      return Number.isFinite(restAngle) ? restAngle : 0;
    }
    const duration = Math.max(1, getRotateDurationMs(settings));
    const elapsed = Math.max(0, now - continuousStart);
    const direction = settings.rotateReverse ? -1 : 1;
    return (Number.isFinite(restAngle) ? restAngle : 0) + direction * ((elapsed / duration) * 360);
  }
  const startTime = Number(stamp.dataset.sequenceRotateStart);
  const from = Number(stamp.dataset.sequenceRotateFrom);
  const to = Number(stamp.dataset.sequenceRotateTo);
  if (!Number.isFinite(startTime) || !Number.isFinite(from) || !Number.isFinite(to)) {
    return 0;
  }
  const duration = Number.isFinite(Number(stamp.dataset.sequenceRotateDuration))
    ? Math.max(1, Number(stamp.dataset.sequenceRotateDuration))
    : getRotateDurationMs(settings);
  const progress = clamp((now - startTime) / duration, 0, 1);
  const eased = progress < 0.5
    ? 2 * progress * progress
    : 1 - Math.pow(-2 * progress + 2, 2) / 2;
  if (progress >= 1) {
    delete stamp.dataset.sequenceRotateStart;
    delete stamp.dataset.sequenceRotateFrom;
    delete stamp.dataset.sequenceRotateTo;
    delete stamp.dataset.sequenceRotateDuration;
    return 0;
  }
  return from + (to - from) * eased;
}

function triggerStampSequenceEffect(stamp, effect, trigger, settings, pool, index, now, currentSource = "") {
  if (!trigger.active || !trigger.key || stamp.dataset.sequenceTriggerKey === trigger.key) {
    return;
  }
  stamp.dataset.sequenceTriggerKey = trigger.key;
  const rawTriggerStartTime = Number.isFinite(Number(trigger.startTime))
    ? Number(trigger.startTime)
    : now;
  const triggerStartTime = Math.min(now, rawTriggerStartTime - SEQUENCE_TRIGGER_PRIME_MS);

  if (effect === "show-hide") {
    const baseOpacity = clamp(Number(stamp.dataset.sequenceBaseOpacity) || 1, 0, 1);
    const isHidden = stamp.dataset.sequenceHidden === "1";
    const nextHidden = !isHidden;
    const currentOpacity = getCurrentSequenceOpacity(stamp, settings, now);
    const targetOpacity = nextHidden ? 0 : baseOpacity;
    stamp.dataset.sequenceHidden = nextHidden ? "1" : "0";
    stamp.dataset.sequenceVisibilityStart = String(triggerStartTime);
    stamp.dataset.sequenceVisibilityFrom = String(settings.showHideFade ? currentOpacity : targetOpacity);
    stamp.dataset.sequenceVisibilityTo = String(targetOpacity);
    stamp.dataset.sequenceVisibilityDuration = String(settings.showHideFade ? Math.max(1, settings.showHideFadeLength) : 1);
  } else if (effect === "move") {
    const currentMove = getCurrentSequenceMove(stamp, settings, now);
    const targetMove = getSequenceMoveTarget(stamp, trigger, settings, index);
    if (settings.moveMode === "circle") {
      if (!Number.isFinite(Number(stamp.dataset.sequenceMoveStart))) {
        stamp.dataset.sequenceMoveStart = String(triggerStartTime);
        stamp.dataset.sequenceMoveCircleStep = String(index * 0.37);
      }
    } else {
      const isInstant = settings.moveInstant && settings.moveMode !== "circle";
      stamp.dataset.sequenceMoveStart = String(triggerStartTime);
      stamp.dataset.sequenceMoveFromX = String(isInstant ? targetMove.x : currentMove.x);
      stamp.dataset.sequenceMoveFromY = String(isInstant ? targetMove.y : currentMove.y);
      stamp.dataset.sequenceMoveToX = String(targetMove.x);
      stamp.dataset.sequenceMoveToY = String(targetMove.y);
      stamp.dataset.sequenceMoveDuration = String(isInstant ? 1 : getMoveDurationMs(settings));
      if (Object.prototype.hasOwnProperty.call(targetMove, "expanded")) {
        stamp.dataset.sequenceMoveExpanded = targetMove.expanded ? "1" : "0";
      }
      if (Object.prototype.hasOwnProperty.call(targetMove, "circleStep")) {
        stamp.dataset.sequenceMoveCircleStep = String(targetMove.circleStep);
      }
    }
  } else if (effect === "rotate") {
    if (settings.rotateContinuous) {
      const currentRotation = getCurrentSequenceRotation(stamp, settings, now);
      const isActive = stamp.dataset.sequenceRotateContinuousActive === "1";
      if (isActive) {
        delete stamp.dataset.sequenceRotateContinuousActive;
        delete stamp.dataset.sequenceRotateContinuousStart;
        stamp.dataset.sequenceRotateStart = String(triggerStartTime);
        stamp.dataset.sequenceRotateFrom = String(currentRotation);
        stamp.dataset.sequenceRotateTo = String(currentRotation);
        stamp.dataset.sequenceRotateDuration = String(SEQUENCE_INTERRUPT_TWEEN_MS);
        stamp.dataset.sequenceRotateRestAngle = String(currentRotation);
      } else {
        delete stamp.dataset.sequenceRotateStart;
        delete stamp.dataset.sequenceRotateFrom;
        delete stamp.dataset.sequenceRotateTo;
        delete stamp.dataset.sequenceRotateDuration;
        stamp.dataset.sequenceRotateRestAngle = String(currentRotation);
        stamp.dataset.sequenceRotateContinuousStart = String(triggerStartTime);
        stamp.dataset.sequenceRotateContinuousActive = "1";
      }
    } else {
      const currentRotation = getCurrentSequenceRotation(stamp, settings, now);
      const direction = settings.rotateReverse ? -1 : 1;
      stamp.dataset.sequenceRotateStart = String(triggerStartTime);
      stamp.dataset.sequenceRotateFrom = String(currentRotation);
      stamp.dataset.sequenceRotateTo = String(currentRotation + direction * 360);
      stamp.dataset.sequenceRotateDuration = String(getRotateDurationMs(settings));
    }
  } else if (effect === "scale") {
    const targetScale = stamp.dataset.sequenceScaleExpanded === "1"
      ? 1
      : 1 + Math.max(0, settings.scaleAmount) / 100;
    const currentScale = getCurrentSequenceScale(stamp, settings, now);
    const isInterruptingToDefault = targetScale === 1 && Math.abs(currentScale - targetScale) > 0.001;
    stamp.dataset.sequenceScaleStart = String(triggerStartTime);
    stamp.dataset.sequenceScaleFrom = String(currentScale);
    stamp.dataset.sequenceScaleTo = String(targetScale);
    stamp.dataset.sequenceScaleDuration = String(
      Math.max(getScaleDurationMs(settings), isInterruptingToDefault ? SEQUENCE_INTERRUPT_TWEEN_MS : 1)
    );
    stamp.dataset.sequenceScaleTarget = String(targetScale);
    stamp.dataset.sequenceScaleExpanded = targetScale === 1 ? "0" : "1";
  } else if (effect === "color-cycle") {
    const currentAmount = getCurrentSequenceColorAmount(stamp, settings, now);
    const nextShifted = stamp.dataset.sequenceColorShifted !== "1";
    const targetAmount = nextShifted ? settings.colorCycleAmount : 0;
    const isInstant = settings.colorCycleInstant;
    stamp.dataset.sequenceColorStart = String(triggerStartTime);
    stamp.dataset.sequenceColorFrom = String(isInstant ? targetAmount : currentAmount);
    stamp.dataset.sequenceColorTo = String(targetAmount);
    stamp.dataset.sequenceColorTarget = String(targetAmount);
    stamp.dataset.sequenceColorDuration = String(isInstant ? 1 : getColorCycleDurationMs(settings));
    stamp.dataset.sequenceColorShifted = nextShifted ? "1" : "0";
  } else if (effect === "image-cycle") {
    triggerImageCycleSequence(stamp, trigger, settings, pool, index, currentSource);
  }
}

function runLayerSequences(now = performance.now()) {
  const imageCyclePool = getSequenceBrushPool();
  for (const stroke of state.strokes) {
    if (!stroke || !Array.isArray(stroke.elements)) {
      continue;
    }
    if (isStrokeSequencePaused(stroke)) {
      if (!Number.isFinite(Number(stroke.sequencePauseStartTime))) {
        stroke.sequencePauseStartTime = now;
      }
      continue;
    }
    if (Number.isFinite(Number(stroke.sequencePauseStartTime))) {
      const pausedDuration = Math.max(0, now - Number(stroke.sequencePauseStartTime));
      if (Array.isArray(stroke.sequenceSlotRuntimes)) {
        for (const runtime of stroke.sequenceSlotRuntimes) {
          if (!runtime || typeof runtime !== "object") {
            continue;
          }
          if (Number.isFinite(Number(runtime.pulseBaseTime))) {
            runtime.pulseBaseTime += pausedDuration;
          }
          if (Number.isFinite(Number(runtime.baseTime))) {
            runtime.baseTime += pausedDuration;
          }
          if (Number.isFinite(Number(runtime.nextTriggerTime))) {
            runtime.nextTriggerTime += pausedDuration;
          }
        }
      }
      for (const stamp of stroke.elements) {
        for (const key of Object.keys(stamp?.dataset || {})) {
          if (
            key.endsWith("Start") ||
            key.endsWith("StartTime") ||
            key.endsWith("MoveStart") ||
            key.endsWith("RotateStart") ||
            key.endsWith("ScaleStart") ||
            key.endsWith("ColorStart") ||
            key.endsWith("VisibilityStart")
          ) {
            const value = Number(stamp.dataset[key]);
            if (Number.isFinite(value)) {
              stamp.dataset[key] = String(value + pausedDuration);
            }
          }
        }
      }
      delete stroke.sequencePauseStartTime;
    }
    const slots = getLayerSequenceSlots(stroke).filter((slot) =>
      isImplementedLayerSequenceEffect(slot.effect)
    );
    if (!isLayerSequenceEnabled(stroke) || !slots.length) {
      resetStrokeSequenceRuntime(stroke);
      for (const stamp of stroke.elements) {
        resetStampSequenceStyle(stamp);
      }
      continue;
    }
    if (stroke.hidden) {
      resetStrokeSequenceRuntime(stroke);
      for (const stamp of stroke.elements) {
        resetStampSequenceStyle(stamp);
      }
      continue;
    }

    const total = stroke.elements.length;
    const visuals = stroke.elements.map((stamp) => {
      ensureStampSequenceBase(stamp);
      stamp.dataset.sequenceActive = "1";
      return {
        opacity: clamp(Number(stamp.dataset.sequenceBaseOpacity) || 1, 0, 1),
        moveX: 0,
        moveY: 0,
        rotationOffset: 0,
        scale: 1,
        tintSettings: getStampBaseTintSettings(stamp),
        sourceUrl: stamp.dataset.sequenceBaseSrc || stamp.dataset.brushUrl || stamp.getAttribute("src") || ""
      };
    });

    if (!Array.isArray(stroke.sequenceSlotRuntimes)) {
      stroke.sequenceSlotRuntimes = [];
    }

    for (let slotIndex = 0; slotIndex < slots.length; slotIndex += 1) {
      const slot = slots[slotIndex];
      const effect = slot.effect;
      const timingStyle = slot.timingStyle;
      const settings = normalizeLayerSequenceSettings(slot.settings);
      const effectDuration = getSequenceEffectDuration(effect, settings);
      const runtimeHost = {
        sequenceRuntime: cloneSequenceRuntime(stroke.sequenceSlotRuntimes[slotIndex])
      };

      for (let index = 0; index < total; index += 1) {
        const stamp = stroke.elements[index];
        const visual = visuals[index];
        if (!stamp || stamp.parentElement !== world || !visual) {
          continue;
        }
        loadSequenceSlotScratch(stamp, slotIndex);
        const currentImageCycleSource = effect === "image-cycle"
          ? getCurrentSequenceImageSource(stamp, visual.sourceUrl)
          : visual.sourceUrl;

        const trigger = getLayerSequenceTrigger(
          stroke,
          index,
          total,
          timingStyle,
          settings,
          now,
          effectDuration,
          runtimeHost
        );
        triggerStampSequenceEffect(
          stamp,
          effect,
          trigger,
          settings,
          imageCyclePool,
          index,
          now,
          currentImageCycleSource
        );

        if (effect === "show-hide") {
          const baseOpacity = clamp(Number(stamp.dataset.sequenceBaseOpacity) || 1, 0, 1);
          const currentOpacity = clamp(getCurrentSequenceOpacity(stamp, settings, now), 0, 1);
          const opacityFactor = baseOpacity > 0 ? currentOpacity / baseOpacity : currentOpacity;
          visual.opacity *= clamp(opacityFactor, 0, 1);
        } else if (effect === "move") {
          const move = getCurrentSequenceMove(stamp, settings, now);
          visual.moveX += move.x;
          visual.moveY += move.y;
        } else if (effect === "rotate") {
          visual.rotationOffset += getCurrentSequenceRotation(stamp, settings, now);
        } else if (effect === "scale") {
          visual.scale *= getCurrentSequenceScale(stamp, settings, now);
        } else if (effect === "color-cycle") {
          const amount = getCurrentSequenceColorAmount(stamp, settings, now);
          if (amount > 0) {
            visual.tintSettings = createLayeredTintSettings(visual.tintSettings, {
              color: settings.colorCycleColor,
              amountPercent: amount
            });
          }
        } else if (effect === "image-cycle") {
          visual.sourceUrl = getCurrentSequenceImageSource(stamp, currentImageCycleSource);
        }

        commitSequenceSlotScratch(stamp, slotIndex);
      }

      stroke.sequenceSlotRuntimes[slotIndex] = cloneSequenceRuntime(runtimeHost.sequenceRuntime);
    }

    for (let index = 0; index < total; index += 1) {
      const stamp = stroke.elements[index];
      const visual = visuals[index];
      if (!stamp || stamp.parentElement !== world || !visual) {
        continue;
      }
      const baseRotation = Number(stamp.dataset.rotation) || 0;
      stamp.style.opacity = String(clamp(visual.opacity, 0, 1));
      setStampSequenceImage(stamp, visual.sourceUrl);
      applyBrushTintStyle(stamp, false, visual.tintSettings);
      stamp.style.transform =
        `translate(${visual.moveX}px, ${visual.moveY}px) rotate(${baseRotation + visual.rotationOffset}deg) scale(${visual.scale})`;
    }
  }
}

function applyLayerSequences(now = performance.now()) {
  if (!state.sequenceExportActive) {
    runLayerSequences(now);
  }
  state.sequenceRafId = window.requestAnimationFrame(applyLayerSequences);
}

function startLayerSequenceLoop() {
  if (state.sequenceRafId !== null) {
    return;
  }
  state.sequenceRafId = window.requestAnimationFrame(applyLayerSequences);
}

function renderEditLayers() {
  if (!editLayerList) {
    return;
  }

  editLayerList.innerHTML = "";
  if (!state.strokes.length) {
    const empty = document.createElement("p");
    empty.className = "empty-panel-label";
    empty.textContent = "no layers";
    editLayerList.appendChild(empty);
    return;
  }

  const fragment = document.createDocumentFragment();
  const topFirstStrokes = state.strokes.slice().reverse();
  for (const stroke of topFirstStrokes) {
    const entry = document.createElement("div");
    entry.className = "edit-layer-entry";
    entry.classList.toggle("is-sequence-open", Boolean(stroke.sequenceOpen));
    entry.dataset.strokeId = String(stroke.id);

    const row = document.createElement("div");
    row.className = "edit-layer-row";
    row.dataset.strokeId = String(stroke.id);
    row.classList.toggle("is-selected", Number(state.selectedEditLayerId) === stroke.id);
    row.classList.toggle("is-hidden", Boolean(stroke.hidden));
    row.classList.toggle("is-animation-paused", Boolean(stroke.animationPaused));
    row.setAttribute("role", "button");
    row.tabIndex = 0;

    const name = document.createElement("span");
    name.className = "edit-layer-name";
    name.textContent = getStrokeLayerName(stroke);

    const sequenceButton = document.createElement("button");
    sequenceButton.type = "button";
    sequenceButton.className = "edit-layer-sequence-button";
    sequenceButton.dataset.layerAction = "sequence";
    sequenceButton.title = stroke.sequenceOpen ? "Hide sequencing controls" : "Show sequencing controls";
    sequenceButton.setAttribute("aria-label", sequenceButton.title);
    sequenceButton.setAttribute("aria-expanded", String(Boolean(stroke.sequenceOpen)));
    sequenceButton.setAttribute("aria-pressed", String(Boolean(stroke.sequenceOpen)));
    const sequenceIcon = document.createElement("span");
    sequenceIcon.className = "edit-layer-sequence-symbol";
    sequenceIcon.setAttribute("aria-hidden", "true");
    sequenceButton.appendChild(sequenceIcon);

    const animationButton = document.createElement("button");
    animationButton.type = "button";
    animationButton.className = "edit-layer-animation-button";
    animationButton.dataset.layerAction = "animation";
    animationButton.title = stroke.animationPaused ? "Resume layer animation" : "Pause layer animation";
    animationButton.setAttribute("aria-label", animationButton.title);
    animationButton.setAttribute("aria-pressed", String(Boolean(stroke.animationPaused)));
    const animationIcon = document.createElement("span");
    animationIcon.className = "edit-layer-animation-symbol";
    animationIcon.setAttribute("aria-hidden", "true");
    animationButton.appendChild(animationIcon);

    const eyeButton = document.createElement("button");
    eyeButton.type = "button";
    eyeButton.className = "edit-layer-eye-button";
    eyeButton.dataset.layerAction = "visibility";
    eyeButton.textContent = stroke.hidden ? "○" : "👁";
    eyeButton.title = stroke.hidden ? "Show layer" : "Hide layer";
    eyeButton.setAttribute("aria-label", eyeButton.title);
    eyeButton.setAttribute("aria-pressed", String(!stroke.hidden));

    row.appendChild(createEditLayerPreview(stroke));
    row.appendChild(name);
    row.appendChild(sequenceButton);
    row.appendChild(animationButton);
    row.appendChild(eyeButton);

    entry.appendChild(row);
    if (stroke.sequenceOpen) {
      const slotCount = getLayerSequenceSlotCount(stroke);
      for (let slotIndex = 0; slotIndex < slotCount; slotIndex += 1) {
        const sequenceRow = document.createElement("div");
        sequenceRow.className = "edit-layer-sequence-row";
        sequenceRow.dataset.strokeId = String(stroke.id);
        sequenceRow.dataset.sequenceSlotIndex = String(slotIndex);

        const effectLabel = document.createElement("span");
        effectLabel.className = "edit-layer-sequence-label";
        effectLabel.textContent = slotIndex === 0 ? "effect" : `effect ${slotIndex + 1}`;
        const styleLabel = document.createElement("span");
        styleLabel.className = "edit-layer-sequence-label";
        styleLabel.textContent = "style";

        sequenceRow.appendChild(effectLabel);
        sequenceRow.appendChild(
          createLayerSequenceSelect(stroke, "effects", LAYER_SEQUENCE_EFFECT_OPTIONS, slotIndex)
        );
        sequenceRow.appendChild(styleLabel);
        sequenceRow.appendChild(
          createLayerSequenceSelect(stroke, "timing", LAYER_SEQUENCE_TIMING_OPTIONS, slotIndex)
        );
        if (slotIndex === 0) {
          const enabledButton = document.createElement("button");
          enabledButton.type = "button";
          enabledButton.className = "edit-layer-sequence-enable-button";
          enabledButton.dataset.layerAction = "sequence-enabled";
          enabledButton.textContent = "×";
          enabledButton.title = isLayerSequenceEnabled(stroke) ? "Disable sequence effect" : "Enable sequence effect";
          enabledButton.setAttribute("aria-label", enabledButton.title);
          enabledButton.setAttribute("aria-pressed", String(isLayerSequenceEnabled(stroke)));
          enabledButton.classList.toggle("is-disabled", !isLayerSequenceEnabled(stroke));
          sequenceRow.appendChild(enabledButton);
        } else {
          const spacer = document.createElement("span");
          spacer.className = "edit-layer-sequence-row-spacer";
          sequenceRow.appendChild(spacer);
        }
        entry.appendChild(sequenceRow);
        entry.appendChild(createLayerSequenceSettings(stroke, slotIndex));
        const addRemoveRow = createLayerSequenceAddRemoveRow(stroke, slotIndex, slotCount);
        if (addRemoveRow) {
          entry.appendChild(addRemoveRow);
        }
      }
    }

    fragment.appendChild(entry);
  }

  editLayerList.appendChild(fragment);
}

function reflowStrokeDomOrder() {
  for (const stroke of state.strokes) {
    if (!stroke || !Array.isArray(stroke.elements)) {
      continue;
    }
    for (const element of stroke.elements) {
      if (element.parentElement === world) {
        world.appendChild(element);
      }
    }
  }
  scheduleSessionSave();
}

function moveStrokeToVisualIndex(stroke, visualIndex) {
  const currentIndex = state.strokes.indexOf(stroke);
  if (currentIndex < 0) {
    return false;
  }

  state.strokes.splice(currentIndex, 1);
  const targetStateIndex = Math.max(
    0,
    Math.min(state.strokes.length, state.strokes.length - Math.max(0, visualIndex))
  );
  state.strokes.splice(targetStateIndex, 0, stroke);
  reflowStrokeDomOrder();
  renderEditLayers();
  return true;
}

function getEditLayerVisualIndexAt(clientY) {
  if (!editLayerList) {
    return -1;
  }

  const rows = Array.from(editLayerList.querySelectorAll(".edit-layer-row"));
  if (!rows.length) {
    return -1;
  }

  for (let index = 0; index < rows.length; index += 1) {
    const rect = rows[index].getBoundingClientRect();
    if (clientY < rect.top + rect.height / 2) {
      return index;
    }
  }
  return rows.length - 1;
}

function setEditLayerDeleteDropzoneState(visible, hovered = false) {
  if (!editLayerDeleteDropzone) {
    return;
  }
  editLayerDeleteDropzone.hidden = !visible;
  editLayerDeleteDropzone.classList.toggle("is-hovered", Boolean(visible && hovered));
  updateEditLayerDeleteDropzonePosition();
}

function updateEditLayerDeleteDropzonePosition() {
  if (!editLayerDeleteDropzone || editLayerDeleteDropzone.hidden) {
    if (editLayerDeleteDropzone) {
      editLayerDeleteDropzone.classList.remove("is-fixed");
      editLayerDeleteDropzone.style.removeProperty("left");
      editLayerDeleteDropzone.style.removeProperty("bottom");
      editLayerDeleteDropzone.style.removeProperty("width");
    }
    return;
  }

  editLayerDeleteDropzone.classList.remove("is-fixed");
  editLayerDeleteDropzone.style.removeProperty("left");
  editLayerDeleteDropzone.style.removeProperty("bottom");
  editLayerDeleteDropzone.style.removeProperty("width");

  const controlsRect = controlsPanel.getBoundingClientRect();
  const dropzoneRect = editLayerDeleteDropzone.getBoundingClientRect();
  const shouldFix = dropzoneRect.bottom > controlsRect.bottom || dropzoneRect.top < controlsRect.top;
  if (!shouldFix) {
    return;
  }

  const horizontalPadding = 12;
  editLayerDeleteDropzone.classList.add("is-fixed");
  editLayerDeleteDropzone.style.left = `${Math.round(controlsRect.left + horizontalPadding)}px`;
  editLayerDeleteDropzone.style.bottom = `${Math.round(window.innerHeight - controlsRect.bottom + horizontalPadding)}px`;
  editLayerDeleteDropzone.style.width = `${Math.max(80, Math.round(controlsRect.width - horizontalPadding * 2))}px`;
}

function isPointerOverEditLayerDeleteDropzone(event) {
  if (!editLayerDeleteDropzone || editLayerDeleteDropzone.hidden) {
    return false;
  }
  const rect = editLayerDeleteDropzone.getBoundingClientRect();
  return (
    event.clientX >= rect.left &&
    event.clientX <= rect.right &&
    event.clientY >= rect.top &&
    event.clientY <= rect.bottom
  );
}

function startEditLayerRowDrag(row, event) {
  const stroke = state.strokeById.get(Number(row.dataset.strokeId));
  if (!stroke) {
    return;
  }

  event.preventDefault();
  selectEditLayer(stroke.id);
  state.editLayerDrag = {
    pointerId: event.pointerId,
    stroke,
    startY: event.clientY,
    dragging: false,
    overDelete: false
  };
  setEditLayerDeleteDropzoneState(true, false);
  row.classList.add("is-dragging");
}

function updateEditLayerRowDrag(event) {
  const drag = state.editLayerDrag;
  if (!drag || drag.pointerId !== event.pointerId) {
    return;
  }

  event.preventDefault();
  if (Math.abs(event.clientY - drag.startY) >= 3) {
    drag.dragging = true;
  }
  if (!drag.dragging) {
    setEditLayerDeleteDropzoneState(true, false);
    return;
  }

  updateEditLayerDeleteDropzonePosition();
  drag.overDelete = isPointerOverEditLayerDeleteDropzone(event);
  setEditLayerDeleteDropzoneState(true, drag.overDelete);
  if (drag.overDelete) {
    return;
  }

  const visualIndex = getEditLayerVisualIndexAt(event.clientY);
  if (visualIndex >= 0) {
    moveStrokeToVisualIndex(drag.stroke, visualIndex);
  }
}

function stopEditLayerRowDrag(pointerId, event = null) {
  const drag = state.editLayerDrag;
  if (!drag || drag.pointerId !== pointerId) {
    return;
  }
  const shouldDelete =
    drag.dragging &&
    (drag.overDelete || (event ? isPointerOverEditLayerDeleteDropzone(event) : false));
  state.editLayerDrag = null;
  setEditLayerDeleteDropzoneState(false, false);
  if (shouldDelete && pushLayerDeleteAction(drag.stroke)) {
    return;
  }
  renderEditLayers();
}

function getStampLayerStroke(element) {
  if (!(element instanceof HTMLImageElement) || !element.classList.contains("stamp")) {
    return null;
  }
  const strokeId = Number(element.dataset.strokeId);
  return Number.isFinite(strokeId) ? state.strokeById.get(strokeId) || null : null;
}

function setStampWorldPosition(element, left, top) {
  element.style.left = `${left}px`;
  element.style.top = `${top}px`;
  delete element.dataset.worldLeft;
  delete element.dataset.worldTop;
  delete element.dataset.worldRight;
  delete element.dataset.worldBottom;
}

function startEditLayerMove(event) {
  if (state.sidebarTab !== "edit") {
    return false;
  }

  const target = event.target;
  const stamp = target instanceof Element ? target.closest(".stamp") : null;
  const stroke = getStampLayerStroke(stamp);
  if (!stroke || stroke.hidden) {
    return false;
  }

  event.preventDefault();
  hideBrushCursorPreview();
  selectEditLayer(stroke.id);

  const startPoint = screenToWorld(event.clientX, event.clientY);
  const originals = stroke.elements.map((element) => ({
    element,
    left: parseFloat(element.style.left) || 0,
    top: parseFloat(element.style.top) || 0
  }));
  const liveAll = stroke.elements.length < EDIT_LAYER_LIVE_MOVE_LIMIT;
  const liveSet = liveAll
    ? new Set(stroke.elements)
    : new Set(stamp ? [stamp] : []);

  for (const element of liveSet) {
    unregisterStampSpatialCells(element);
  }

  state.editLayerMove = {
    pointerId: event.pointerId,
    stroke,
    startPoint,
    originals,
    liveSet,
    dx: 0,
    dy: 0
  };

  try {
    viewport.setPointerCapture(event.pointerId);
  } catch (error) {
    // Continue without capture if the pointer ended early.
  }
  return true;
}

function updateEditLayerMove(event) {
  const move = state.editLayerMove;
  if (!move || move.pointerId !== event.pointerId) {
    return;
  }

  event.preventDefault();
  const point = screenToWorld(event.clientX, event.clientY);
  move.dx = point.x - move.startPoint.x;
  move.dy = point.y - move.startPoint.y;
  for (const original of move.originals) {
    if (!move.liveSet.has(original.element)) {
      continue;
    }
    setStampWorldPosition(original.element, original.left + move.dx, original.top + move.dy);
  }
  scheduleStampVisibilityRefresh();
}

function stopEditLayerMove(pointerId) {
  const move = state.editLayerMove;
  if (!move || move.pointerId !== pointerId) {
    return;
  }

  if (viewport.hasPointerCapture(pointerId)) {
    viewport.releasePointerCapture(pointerId);
  }

  const viewportBounds = getViewportWorldBounds();
  for (const original of move.originals) {
    unregisterStampSpatialCells(original.element);
    setStampWorldPosition(original.element, original.left + move.dx, original.top + move.dy);
    if (!move.stroke.hidden && original.element.parentElement === world) {
      registerStampSpatialCells(original.element);
      updateStampViewportVisibility(original.element, viewportBounds);
    }
  }

  state.editLayerMove = null;
  scheduleStampVisibilityRefresh();
  scheduleSessionSave();
}

function onBrushGalleryClick(event) {
  const preview = event.target.closest(".brush-thumb");
  if (preview) {
    const previewItem = preview.closest(".brush-item");
    if (!previewItem) {
      return;
    }

    const previewBrushId = Number(previewItem.dataset.brushId);
    const previewBrush = findBrushById(previewBrushId);
    if (!previewBrush) {
      return;
    }

    if (event.ctrlKey || event.metaKey) {
      clearActiveCustomBrushPreset();
      state.soloBrushId = null;
      if (!(state.selectedBrushIds instanceof Set)) {
        state.selectedBrushIds = new Set();
      }
      if (state.selectedBrushIds.has(previewBrush.id)) {
        state.selectedBrushIds.delete(previewBrush.id);
      } else {
        state.selectedBrushIds.add(previewBrush.id);
        previewBrush.enabled = true;
      }
    } else if (state.soloBrushId === previewBrush.id) {
      clearActiveCustomBrushPreset();
      setSoloBrushId(null);
    } else {
      clearActiveCustomBrushPreset();
      setSoloBrushId(previewBrush.id);
      previewBrush.enabled = true;
    }

    updateBrushStatus();
    renderBrushGallery();
    state.shortcutPreview.brushId = null;
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
    updateBrushCursorPreview();
    scheduleSessionSave();
    return;
  }

	  const button = event.target.closest(".brush-action-button, .brush-favorite-overlay-button, .brush-preset-remove-button");
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
    clearActiveCustomBrushPreset();
    brush.enabled = !brush.enabled;
    if (!brush.enabled && state.soloBrushId === brush.id) {
      state.soloBrushId = null;
    }
    if (!brush.enabled && state.selectedBrushIds instanceof Set) {
      state.selectedBrushIds.delete(brush.id);
    }
  } else if (action === "crop") {
    openBrushCropPopup(brush);
    return;
  } else if (action === "favorite") {
    if (!toggleBrushFavorite(brush)) {
      return;
    }
    if (state.activeStockBrushFolderId === "favorites") {
      brush.enabled = isBrushFavorite(brush);
      if (!brush.enabled && state.soloBrushId === brush.id) {
        state.soloBrushId = null;
      }
      if (!brush.enabled && state.selectedBrushIds instanceof Set) {
        state.selectedBrushIds.delete(brush.id);
      }
    }
  } else if (action === "remove-preset") {
    if (!removeBrushFromCustomPreset(brush)) {
      return;
    }
  }

  updateBrushStatus();
  renderBrushGallery();
  state.shortcutPreview.brushId = null;
  state.brushCursorPreview.brushId = null;
  resetBrushCursorPreviewSource();
  updateBrushCursorPreview();
  scheduleSessionSave();
}

function onBrushGalleryContextMenu(event) {
  const preview = event.target.closest(".brush-thumb");
  if (!preview || controlsPanel.dataset.sidebarMode !== "draw") {
    return;
  }

  const item = preview.closest(".brush-item");
  if (!item) {
    return;
  }

  const brush = findBrushById(Number(item.dataset.brushId));
  if (!brush) {
    return;
  }

  event.preventDefault();
  clearActiveCustomBrushPreset();
  brush.enabled = !brush.enabled;
  if (!brush.enabled && state.soloBrushId === brush.id) {
    state.soloBrushId = null;
  }
  if (!brush.enabled && state.selectedBrushIds instanceof Set) {
    state.selectedBrushIds.delete(brush.id);
  }
  state.shortcutPreview.brushId = null;
  state.brushCursorPreview.brushId = null;
  resetBrushCursorPreviewSource();
  updateBrushStatus();
  renderBrushGallery();
  updateBrushCursorPreview();
  scheduleSessionSave();
}

function getBrushFromGalleryEventTarget(target) {
  const item = target?.closest ? target.closest(".brush-item") : null;
  if (!item) {
    return null;
  }
  return findBrushById(Number(item.dataset.brushId));
}

function onBrushGalleryDragStart(event) {
  const brush = getBrushFromGalleryEventTarget(event.target);
  if (!brush) {
    event.preventDefault();
    return;
  }
  const source = getBrushPresetSource(brush);
  if (!source) {
    event.preventDefault();
    return;
  }
  event.dataTransfer.effectAllowed = "copy";
  event.dataTransfer.setData("text/plain", source);
  event.dataTransfer.setData("application/x-image-draw-brush-id", String(brush.id));
  event.dataTransfer.setData("application/x-image-draw-brush-source", source);
  const item = event.target.closest(".brush-item");
  if (item) {
    item.classList.add("is-dragging");
  }
}

function onBrushGalleryDragEnd(event) {
  const item = event.target.closest(".brush-item");
  if (item) {
    item.classList.remove("is-dragging");
  }
}

function getDraggedBrushForPresetDrop(event) {
  const brushId = Number(event.dataTransfer.getData("application/x-image-draw-brush-id"));
  if (Number.isFinite(brushId)) {
    const brush = findBrushById(brushId);
    if (brush) {
      return brush;
    }
  }
  const source = normalizeFavoriteBrushSource(
    event.dataTransfer.getData("application/x-image-draw-brush-source") ||
      event.dataTransfer.getData("text/plain")
  );
  if (!source) {
    return null;
  }
  return state.brushes.find((brush) => getBrushPresetSource(brush) === source) || null;
}

function onCustomBrushPresetDragOver(event) {
  const button = event.target.closest(".custom-brush-preset-button");
  if (!button || button.disabled) {
    return;
  }
  event.preventDefault();
  event.dataTransfer.dropEffect = "copy";
}

function onCustomBrushPresetDrop(event) {
  const button = event.target.closest(".custom-brush-preset-button");
  if (!button || button.disabled) {
    return;
  }
  event.preventDefault();
  const brush = getDraggedBrushForPresetDrop(event);
  if (!brush) {
    return;
  }
  const presetIndex = normalizeCustomBrushPresetIndex(button.dataset.presetIndex);
  if (presetIndex === null || !addBrushToCustomPreset(brush, presetIndex)) {
    return;
  }
  updateBrushStatus(`Added ${brush.name} to preset ${presetIndex + 1}.`);
  scheduleSessionSave();
}

function onCustomBrushPresetClick(event) {
  const button = event.target.closest(".custom-brush-preset-button");
  if (!button || button.disabled) {
    return;
  }
  event.preventDefault();
  void loadCustomBrushPreset(button.dataset.presetIndex);
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
  scheduleStampVisibilityRefresh();
  if (state.exportMode) {
    updateExportOverlayGeometry();
  }
  if (state.shapeDraft) {
    updateShapePreview(
      state.shapeDraft.mode,
      state.shapeDraft.anchorX,
      state.shapeDraft.anchorY,
      state.shapeDraft.currentX,
      state.shapeDraft.currentY
    );
  }
  updateBrushCursorPreview();
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
    unregisterStampSpatialCells(element);
    decrementUrlRef(element.dataset.brushUrl);
    if (element.parentElement === world) {
      element.remove();
      state.stampCount = Math.max(0, state.stampCount - 1);
    }
  }
  scheduleStampVisibilityRefresh();
}

function appendStrokeToWorld(stroke) {
  const viewportBounds = getViewportWorldBounds();
  const hidden = Boolean(stroke.hidden);
  for (const element of stroke.elements) {
    if (element.parentElement !== world) {
      state.stampCount += 1;
    }
    world.appendChild(element);
    element.classList.toggle("is-layer-hidden", hidden);
    if (!hidden) {
      registerStampSpatialCells(element);
      updateStampViewportVisibility(element, viewportBounds);
    }
    applyGifPauseStateToImage(element);
    incrementUrlRef(element.dataset.brushUrl);
  }
  scheduleStampVisibilityRefresh();
}

function pushHistoryAction(action) {
  state.redoHistory = [];
  state.history.push(action);
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
}

function pushStroke(stroke) {
  if (!stroke.elements.length) {
    return;
  }

  state.strokes.push(stroke);
  state.strokeById.set(stroke.id, stroke);
  updateRememberedExportSetupForAddedStroke(stroke);
  pushHistoryAction({ type: "draw", stroke });
}

function pushEraseAction(removals) {
  if (!Array.isArray(removals) || !removals.length) {
    return;
  }
  pushHistoryAction({ type: "erase", removals });
}

function pushLayerDeleteAction(stroke) {
  if (!stroke) {
    return false;
  }

  const strokeIndex = state.strokes.indexOf(stroke);
  if (strokeIndex < 0) {
    return false;
  }

  detachStrokeFromWorld(stroke);
  removeStrokeFromState(stroke);
  if (Number(state.selectedEditLayerId) === Number(stroke.id)) {
    state.selectedEditLayerId = null;
  }
  pushHistoryAction({ type: "layer-delete", stroke, strokeIndex });
  return true;
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
      state.stampCount += 1;
      registerStampSpatialCells(removal.element);
      updateStampViewportVisibility(removal.element);
      applyGifPauseStateToImage(removal.element);
      incrementUrlRef(removal.element.dataset.brushUrl);
    }
  }
  scheduleStampVisibilityRefresh();
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
  if (!state.strokeById.has(stroke.id)) {
    state.strokes.push(stroke);
    state.strokeById.set(stroke.id, stroke);
  }
  appendStrokeToWorld(stroke);
  updateRememberedExportSetupForAddedStroke(stroke);
  return true;
}

function undoLayerDeleteAction(action) {
  const stroke = action.stroke;
  if (!stroke || state.strokeById.has(stroke.id)) {
    return true;
  }

  const preferredIndex =
    Number.isFinite(Number(action.strokeIndex)) && Number(action.strokeIndex) >= 0
    ? Number(action.strokeIndex)
    : state.strokes.length;
  const insertIndex = Math.max(0, Math.min(preferredIndex, state.strokes.length));
  state.strokes.splice(insertIndex, 0, stroke);
  state.strokeById.set(stroke.id, stroke);
  appendStrokeToWorld(stroke);
  reflowStrokeDomOrder();
  selectEditLayer(stroke.id);
  return true;
}

function redoLayerDeleteAction(action) {
  const stroke = action.stroke;
  if (!stroke || !state.strokeById.has(stroke.id)) {
    return true;
  }

  detachStrokeFromWorld(stroke);
  removeStrokeFromState(stroke);
  if (Number(state.selectedEditLayerId) === Number(stroke.id)) {
    state.selectedEditLayerId = null;
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
  } else if (action.type === "layer-delete") {
    undoLayerDeleteAction(action);
  } else {
    state.history.push(action);
    return;
  }

  state.redoHistory.push(action);
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
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
  } else if (action.type === "layer-delete") {
    applied = redoLayerDeleteAction(action);
  }

  if (!applied) {
    return;
  }

  state.redoHistory.pop();
  state.history.push(action);
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
}

function clearAllStrokes() {
  while (state.strokes.length) {
    const stroke = state.strokes.pop();
    detachStrokeFromWorld(stroke);
  }
  clearStampSpatialIndex();
  state.stampCount = 0;
  if (state.exportMode) {
    exitExportMode();
  }
  clearRememberedExportSetup();
  state.strokeById.clear();
  state.history = [];
  state.redoHistory = [];
  clearCursorTrail();
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
}

function getBrushWeight(brush) {
  const mode = normalizeBrushWeightMode(brush?.weightMode);
  return BRUSH_WEIGHT_MULTIPLIERS[mode] || 1;
}

function pickRandomBrush() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    return soloBrush;
  }

  const selectedBrushes = getSelectedBrushes();
  const candidates = selectedBrushes.length
    ? selectedBrushes
    : state.brushes.filter((brush) => brush.enabled);
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

function ensureDrawableBrushes() {
  if (!state.brushes.length) {
    updateBrushStatus("Load brush data before drawing.");
    return false;
  }

  if (!hasEnabledBrushes()) {
    updateBrushStatus("Enable at least one brush image before drawing.");
    return false;
  }

  return true;
}

function getSpacingValue() {
  return Math.max(1, mapSpacingSliderToValue(spacingSlider.value));
}

function getSpraySpreadValue() {
  return Math.max(1, Number(spraySpreadSlider.value) || 1);
}

function getSprayStampCount(spread) {
  const spacing = getSpacingValue();
  const density = Math.max(1, spread / Math.max(1, spacing));
  return clamp(Math.round(density * density * 3), SPRAY_MIN_STAMPS, SPRAY_MAX_STAMPS);
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

  const { width, height } = getBrushPlacementSize(brush);
  const stamp = document.createElement("img");

  stamp.className = "stamp";
  stamp.src = brush.url;
  stamp.alt = "";
  stamp.draggable = false;
  stamp.loading = "lazy";
  stamp.decoding = "async";
  stamp.dataset.brushUrl = brush.url;
  stamp.dataset.brushId = String(brush.id);
  stamp.dataset.strokeId = String(stroke.id);
  applyGifPauseStateToImage(stamp);
  stamp.style.width = `${width}px`;
  stamp.style.height = `${height}px`;
  stamp.style.left = `${x - width / 2}px`;
  stamp.style.top = `${y - height / 2}px`;
  const rotation = parseNumericInputValue(rotationSlider, 0);
  stamp.dataset.rotation = String(rotation);
  stamp.style.opacity = String(clamp(Number(opacitySlider.value) / 100, 0, 1));
  stamp.dataset.sequenceBaseOpacity = stamp.style.opacity;
  stamp.dataset.sequenceBaseSrc = brush.url;
  stamp.style.imageRendering = renderModeToggle.checked ? "auto" : "pixelated";
  stamp.style.transform = `rotate(${rotation}deg)`;
  const tintSettings = getCurrentTintSettings();
  setElementTintData(stamp, tintSettings);
  applyBrushTintStyle(stamp, false, tintSettings);

  world.appendChild(stamp);
  state.stampCount += 1;
  registerStampSpatialCells(stamp);
  updateStampViewportVisibility(stamp);
  incrementUrlRef(brush.url);
  stroke.elements.push(stamp);
  scheduleStampVisibilityRefresh();
  return true;
}

function placeSpray(x, y, stroke) {
  const spread = getSpraySpreadValue();
  const stampCount = getSprayStampCount(spread);
  let placedAny = false;

  for (let index = 0; index < stampCount; index += 1) {
    const angle = Math.random() * Math.PI * 2;
    const radius = Math.sqrt(Math.random()) * spread;
    if (placeBrush(x + Math.cos(angle) * radius, y + Math.sin(angle) * radius, stroke)) {
      placedAny = true;
    } else if (getVisibleStampCount() >= MAX_VISIBLE_STAMPS) {
      break;
    }
  }

  return placedAny;
}

async function maybeYieldForPlacement(task, placedCount) {
  throwIfTaskCancelled(task);
  if (placedCount > 0 && placedCount % PLACEMENT_CANCEL_CHECK_INTERVAL === 0) {
    await yieldToMainThread(task);
  }
}

async function placeLineBrushes(stroke, startX, startY, endX, endY, task = null) {
  let placedAny = placeBrush(startX, startY, stroke);
  await maybeYieldForPlacement(task, stroke.elements.length);
  const spacing = getSpacingValue();
  const dx = endX - startX;
  const dy = endY - startY;
  const distance = Math.hypot(dx, dy);
  if (distance === 0) {
    return placedAny;
  }

  const capacity = MAX_VISIBLE_STAMPS - getVisibleStampCount();
  const stepX = dx / distance;
  const stepY = dy / distance;
  let traveled = spacing;
  let placedAfterStart = 0;
  while (traveled <= distance && placedAfterStart < capacity) {
    throwIfTaskCancelled(task);
    if (!placeBrush(startX + stepX * traveled, startY + stepY * traveled, stroke)) {
      break;
    }
    placedAny = true;
    placedAfterStart += 1;
    traveled += spacing;
    await maybeYieldForPlacement(task, stroke.elements.length);
  }

  return placedAny;
}

function getRectBoundsFromPoints(startX, startY, endX, endY) {
  return {
    left: Math.min(startX, endX),
    top: Math.min(startY, endY),
    right: Math.max(startX, endX),
    bottom: Math.max(startY, endY)
  };
}

function getCircleBoundsFromPoints(startX, startY, endX, endY) {
  const size = Math.max(Math.abs(endX - startX), Math.abs(endY - startY));
  return {
    left: endX >= startX ? startX : startX - size,
    top: endY >= startY ? startY : startY - size,
    right: endX >= startX ? startX + size : startX,
    bottom: endY >= startY ? startY + size : startY
  };
}

function getGridAxisPositions(min, max, spacing) {
  const size = Math.max(0, max - min);
  const count = Math.max(1, Math.floor(size / spacing) + 1);
  const usedSize = (count - 1) * spacing;
  const start = min + (size - usedSize) / 2;
  const positions = [];
  for (let index = 0; index < count; index += 1) {
    positions.push(start + index * spacing);
  }
  return positions;
}

async function placeRectBrushes(stroke, startX, startY, endX, endY, task = null) {
  const bounds = getRectBoundsFromPoints(startX, startY, endX, endY);
  const spacing = getSpacingValue();
  const xPositions = getGridAxisPositions(bounds.left, bounds.right, spacing);
  const yPositions = getGridAxisPositions(bounds.top, bounds.bottom, spacing);
  const capacity = MAX_VISIBLE_STAMPS - getVisibleStampCount();
  let placedAny = false;
  if (capacity <= 0) {
    notifyStampLimitReached();
    return false;
  }

  for (const y of yPositions) {
    for (const x of xPositions) {
      throwIfTaskCancelled(task);
      if (stroke.elements.length >= capacity) {
        return placedAny;
      }
      if (!placeBrush(x, y, stroke)) {
        return placedAny;
      }
      placedAny = true;
      await maybeYieldForPlacement(task, stroke.elements.length);
    }
  }

  return placedAny;
}

async function placeCircleBrushes(stroke, startX, startY, endX, endY, task = null) {
  const bounds = getCircleBoundsFromPoints(startX, startY, endX, endY);
  const spacing = getSpacingValue();
  const xPositions = getGridAxisPositions(bounds.left, bounds.right, spacing);
  const yPositions = getGridAxisPositions(bounds.top, bounds.bottom, spacing);
  const centerX = (bounds.left + bounds.right) / 2;
  const centerY = (bounds.top + bounds.bottom) / 2;
  const radius = Math.max(0, (bounds.right - bounds.left) / 2);
  const radiusSq = radius * radius;
  const capacity = MAX_VISIBLE_STAMPS - getVisibleStampCount();
  let placedAny = false;
  if (capacity <= 0) {
    notifyStampLimitReached();
    return false;
  }

  for (const y of yPositions) {
    for (const x of xPositions) {
      throwIfTaskCancelled(task);
      const dx = x - centerX;
      const dy = y - centerY;
      if (dx * dx + dy * dy > radiusSq) {
        continue;
      }
      if (stroke.elements.length >= capacity) {
        return placedAny;
      }
      if (!placeBrush(x, y, stroke)) {
        return placedAny;
      }
      placedAny = true;
      await maybeYieldForPlacement(task, stroke.elements.length);
    }
  }

  throwIfTaskCancelled(task);
  if (!placedAny) {
    placedAny = placeBrush(centerX, centerY, stroke);
  }
  return placedAny;
}

function setShapePreviewBox(bounds, className) {
  const topLeft = worldToScreen(bounds.left, bounds.top);
  const bottomRight = worldToScreen(bounds.right, bounds.bottom);
  const left = Math.min(topLeft.x, bottomRight.x);
  const top = Math.min(topLeft.y, bottomRight.y);
  const width = Math.abs(bottomRight.x - topLeft.x);
  const height = Math.abs(bottomRight.y - topLeft.y);
  shapePreview.className = `is-visible ${className}`;
  shapePreview.style.left = `${left}px`;
  shapePreview.style.top = `${top}px`;
  shapePreview.style.width = `${width}px`;
  shapePreview.style.height = `${height}px`;
  shapePreview.style.transform = "none";
}

function updateShapePreview(mode, startX, startY, endX, endY) {
  if (mode === "line") {
    const start = worldToScreen(startX, startY);
    const end = worldToScreen(endX, endY);
    const dx = end.x - start.x;
    const dy = end.y - start.y;
    shapePreview.className = "is-visible is-line";
    shapePreview.style.left = `${start.x}px`;
    shapePreview.style.top = `${start.y}px`;
    shapePreview.style.width = `${Math.hypot(dx, dy)}px`;
    shapePreview.style.height = "0";
    shapePreview.style.transform = `rotate(${Math.atan2(dy, dx)}rad)`;
    return;
  }

  if (mode === "box") {
    setShapePreviewBox(getRectBoundsFromPoints(startX, startY, endX, endY), "is-box");
    return;
  }

  if (mode === "circle") {
    setShapePreviewBox(getCircleBoundsFromPoints(startX, startY, endX, endY), "is-circle");
  }
}

async function commitShapeStroke(mode, startX, startY, endX, endY) {
  if (state.placementTask) {
    return false;
  }

  const task = createCancellableTask("placement");
  const stroke = {
    id: state.nextStrokeId,
    layerNumber: state.nextStrokeId,
    layerType: normalizeStrokeLayerType(mode),
    brushCategoryName: getActiveBrushCategoryName(),
    elements: []
  };
  state.nextStrokeId += 1;
  state.placementTask = task;
  updateBrushStatus("Placing brush batch... Press Esc to cancel.");
  updateBrushCursorPreview();
  updateUndoState();

  try {
    if (mode === "line") {
      await placeLineBrushes(stroke, startX, startY, endX, endY, task);
    } else if (mode === "box") {
      await placeRectBrushes(stroke, startX, startY, endX, endY, task);
    } else if (mode === "circle") {
      await placeCircleBrushes(stroke, startX, startY, endX, endY, task);
    }

    throwIfTaskCancelled(task);
    pushStroke(stroke);
    return stroke.elements.length > 0;
  } catch (error) {
    detachStrokeFromWorld(stroke);
    if (isCancellationError(error)) {
      updateBrushStatus("Placement cancelled.");
      return false;
    }
    updateBrushStatus("Could not finish brush placement.");
    throw error;
  } finally {
    if (state.placementTask === task) {
      state.placementTask = null;
    }
    updateUndoState();
    updateBrushCursorPreview();
    scheduleStampVisibilityRefresh();
  }
}

function placeAlongPath(drawing, x, y) {
  if (drawing.limitReached) {
    return;
  }

  const spacing = getSpacingValue();
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
    const placed = drawing.mode === "spray"
      ? placeSpray(cursorX, cursorY, drawing.stroke)
      : placeBrush(cursorX, cursorY, drawing.stroke);
    if (!placed) {
      drawing.limitReached = true;
      break;
    }
    remaining -= spacing;
  }

  drawing.lastPlacedX = cursorX;
  drawing.lastPlacedY = cursorY;
}

function updateActiveStrokeTailRotation() {
  if (!state.drawing || !state.drawing.stroke || !state.drawing.stroke.elements.length) {
    return;
  }

  const elements = state.drawing.stroke.elements;
  const tail = elements[elements.length - 1];
  if (!tail) {
    return;
  }

  const rotation = parseNumericInputValue(rotationSlider, 0);
  tail.dataset.rotation = String(rotation);
  tail.style.transform = `rotate(${rotation}deg)`;
  registerStampSpatialCells(tail);
}

function rectsIntersect(a, b) {
  return !(a.right <= b.left || a.left >= b.right || a.bottom <= b.top || a.top >= b.bottom);
}

function getExportSequenceVisualState(element, now = performance.now()) {
  const stroke = getStampLayerStroke(element);
  const baseOpacity = clamp(Number(element.dataset.sequenceBaseOpacity) || Number(element.style.opacity) || 1, 0, 1);
  const currentSource = element.getAttribute("src") || element.currentSrc || "";
  const baseSource = element.dataset.brushUrl || currentSource;
  const visual = {
    opacity: baseOpacity,
    move: { x: 0, y: 0 },
    rotationOffset: 0,
    scale: 1,
    tintSettings: getStampBaseTintSettings(element),
    sourceUrl: baseSource
  };
  if (!stroke || !isLayerSequenceEnabled(stroke)) {
    return visual;
  }
  const slots = getLayerSequenceSlots(stroke).filter((slot) =>
    isImplementedLayerSequenceEffect(slot.effect)
  );
  for (let slotIndex = 0; slotIndex < slots.length; slotIndex += 1) {
    const slot = slots[slotIndex];
    const effect = slot.effect;
    const settings = normalizeLayerSequenceSettings(slot.settings);
    loadSequenceSlotScratch(element, slotIndex);
    if (effect === "show-hide") {
      const currentOpacity = clamp(getCurrentSequenceOpacity(element, settings, now), 0, 1);
      const opacityFactor = baseOpacity > 0 ? currentOpacity / baseOpacity : currentOpacity;
      visual.opacity *= clamp(opacityFactor, 0, 1);
    } else if (effect === "move") {
      const move = getCurrentSequenceMove(element, settings, now);
      visual.move.x += move.x;
      visual.move.y += move.y;
    } else if (effect === "rotate") {
      visual.rotationOffset += getCurrentSequenceRotation(element, settings, now);
    } else if (effect === "scale") {
      visual.scale *= getCurrentSequenceScale(element, settings, now);
    } else if (effect === "color-cycle") {
      const colorCycleAmount = getCurrentSequenceColorAmount(element, settings, now);
      if (colorCycleAmount > 0) {
        visual.tintSettings = createLayeredTintSettings(visual.tintSettings, {
          color: settings.colorCycleColor,
          amountPercent: colorCycleAmount
        });
      }
    } else if (effect === "image-cycle") {
      const sequenceSource = getCurrentSequenceImageSource(element, visual.sourceUrl);
      if (sequenceSource && sequenceSource !== TRANSPARENT_STAMP_SRC) {
        visual.sourceUrl = sequenceSource;
      }
    }
    commitSequenceSlotScratch(element, slotIndex);
  }
  return visual;
}

function createExportStampEntry(element, selectionBounds, sequenceNow = null) {
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  if (width <= 0 || height <= 0) {
    return null;
  }

  const sequenceState = element.dataset.sequenceActive === "1"
    ? getExportSequenceVisualState(element, Number.isFinite(Number(sequenceNow)) ? Number(sequenceNow) : performance.now())
    : null;
  const visualScale = Math.max(0.001, Number(sequenceState?.scale) || 1);
  const visualWidth = width * visualScale;
  const visualHeight = height * visualScale;
  const rotation = (Number(element.dataset.rotation) || 0) + (Number(sequenceState?.rotationOffset) || 0);
  const moveX = Number(sequenceState?.move?.x) || 0;
  const moveY = Number(sequenceState?.move?.y) || 0;
  const bounds = getStampWorldBoundsFromLayout(left + moveX, top + moveY, visualWidth, visualHeight, rotation);
  if (!rectsIntersect(bounds, selectionBounds)) {
    return null;
  }

  return {
    element,
    sourceUrl: sequenceState?.sourceUrl || element.dataset.brushUrl || element.currentSrc || element.getAttribute("src") || "",
    centerX: left + width / 2 + moveX,
    centerY: top + height / 2 + moveY,
    width: visualWidth,
    height: visualHeight,
    rotation,
    opacity: sequenceState ? sequenceState.opacity : clamp(Number(element.style.opacity) || 1, 0, 1),
    tintSettings: sequenceState?.tintSettings || getStampBaseTintSettings(element),
    imageRendering: element.style.imageRendering === "auto" ? "auto" : "pixelated"
  };
}

async function collectExportStampEntries(selectionBounds, task = null, progress = null) {
  const entries = [];
  const stamps = getVisibleStampElements();
  const total = Math.max(1, stamps.length);

  for (let index = 0; index < stamps.length; index += 1) {
    throwIfTaskCancelled(task);
    const entry = createExportStampEntry(stamps[index], selectionBounds);
    if (entry) {
      entries.push(entry);
    }
    if (progress && (index === stamps.length - 1 || index % EXPORT_CANCEL_CHECK_INTERVAL === 0)) {
      progress((index + 1) / total);
    }
    if (index > 0 && index % EXPORT_CANCEL_CHECK_INTERVAL === 0) {
      await yieldToMainThread(task);
    }
  }

  return entries;
}

function refreshExportSequenceEntries(entries, selectionBounds, sequenceNow) {
  if (!Array.isArray(entries)) {
    return;
  }
  for (const entry of entries) {
    const nextEntry = createExportStampEntry(entry.element, selectionBounds, sequenceNow);
    if (nextEntry) {
      Object.assign(entry, nextEntry);
    }
  }
}

function resolveGifFrameSource(animation, timeMs) {
  if (!animation || !Array.isArray(animation.frames) || !animation.frames.length) {
    return null;
  }

  const durations = Array.isArray(animation.durations) ? animation.durations : [];
  const totalDuration = Math.max(1, Number(animation.totalDuration) || 1);
  let wrapped = Number(timeMs) % totalDuration;
  if (wrapped < 0) {
    wrapped += totalDuration;
  }

  let elapsed = 0;
  for (let index = 0; index < animation.frames.length; index += 1) {
    const frameDuration = Math.max(
      1,
      Number.isFinite(Number(durations[index])) ? Number(durations[index]) : EXPORT_GIF_FRAME_DELAY_MS
    );
    elapsed += frameDuration;
    if (wrapped < elapsed) {
      return animation.frames[index];
    }
  }

  return animation.frames[animation.frames.length - 1];
}

async function decodeGifAnimation(url) {
  const bytes = await readImageBytes(url);
  const gifuctModule = await loadGifuctModule();
  const parseInput = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
  const parsed = gifuctModule.parseGIF(parseInput);
  const decodedFrames = gifuctModule.decompressFrames(parsed, true);

  if (!decodedFrames.length) {
    throw new Error("No GIF frames decoded.");
  }

  const width = Math.max(
    1,
    Number(parsed?.lsd?.width) ||
      Number(decodedFrames[0]?.dims?.width) ||
      1
  );
  const height = Math.max(
    1,
    Number(parsed?.lsd?.height) ||
      Number(decodedFrames[0]?.dims?.height) ||
      1
  );

  const compositeCanvas = document.createElement("canvas");
  compositeCanvas.width = width;
  compositeCanvas.height = height;
  const compositeCtx = compositeCanvas.getContext("2d", { alpha: true });
  if (!compositeCtx) {
    throw new Error("Could not create GIF decode canvas.");
  }

  const patchCanvas = document.createElement("canvas");
  const patchCtx = patchCanvas.getContext("2d", { alpha: true });
  if (!patchCtx) {
    throw new Error("Could not create GIF patch canvas.");
  }

  compositeCtx.clearRect(0, 0, width, height);

  const frames = [];
  const durations = [];

  for (const frame of decodedFrames) {
    const dims = frame?.dims || {};
    const left = Number.isFinite(Number(dims.left)) ? Number(dims.left) : 0;
    const top = Number.isFinite(Number(dims.top)) ? Number(dims.top) : 0;
    const frameWidth = Math.max(1, Number(dims.width) || width);
    const frameHeight = Math.max(1, Number(dims.height) || height);
    const disposalType = Number(frame?.disposalType) || 0;

    let restoreBeforeFrame = null;
    if (disposalType === 3) {
      restoreBeforeFrame = compositeCtx.getImageData(0, 0, width, height);
    }

    if (frame?.patch && frame.patch.length === frameWidth * frameHeight * 4) {
      const patchData = new Uint8ClampedArray(frame.patch);
      const patchImage = new ImageData(patchData, frameWidth, frameHeight);
      if (patchCanvas.width !== frameWidth) {
        patchCanvas.width = frameWidth;
      }
      if (patchCanvas.height !== frameHeight) {
        patchCanvas.height = frameHeight;
      }
      patchCtx.clearRect(0, 0, frameWidth, frameHeight);
      patchCtx.putImageData(patchImage, 0, 0);
      compositeCtx.drawImage(patchCanvas, left, top);
    }

    const snapshotCanvas = document.createElement("canvas");
    snapshotCanvas.width = width;
    snapshotCanvas.height = height;
    const snapshotCtx = snapshotCanvas.getContext("2d", { alpha: true });
    if (!snapshotCtx) {
      throw new Error("Could not create GIF frame canvas.");
    }
    snapshotCtx.drawImage(compositeCanvas, 0, 0);
    frames.push(snapshotCanvas);

    const delayMs = Number(frame?.delay);
    durations.push(
      Math.max(20, Number.isFinite(delayMs) && delayMs > 0 ? delayMs : EXPORT_GIF_FRAME_DELAY_MS)
    );

    if (disposalType === 2) {
      compositeCtx.clearRect(left, top, frameWidth, frameHeight);
    } else if (disposalType === 3 && restoreBeforeFrame) {
      compositeCtx.putImageData(restoreBeforeFrame, 0, 0);
    }
  }

  const totalDuration =
    durations.reduce((sum, duration) => sum + duration, 0) || EXPORT_GIF_FRAME_DELAY_MS;

  return { frames, durations, totalDuration };
}

function getSequenceExportSourceUrls() {
  const urls = [];
  const hasImageCycleSequence = state.strokes.some(
    (stroke) =>
      isLayerSequenceEnabled(stroke) &&
      !stroke.hidden &&
      getLayerSequenceSlots(stroke).some((slot) => slot.effect === "image-cycle")
  );
  if (!hasImageCycleSequence) {
    return urls;
  }
  for (const brush of getSequenceBrushPool()) {
    if (brush?.url) {
      urls.push(brush.url);
    }
  }
  return urls;
}

async function buildGifAnimationMap(entries, task = null, progress = null, extraUrls = []) {
  const urls = new Set();
  for (const entry of entries) {
    if (!entry || !isGifUrl(entry.sourceUrl)) {
      continue;
    }
    urls.add(entry.sourceUrl);
  }
  for (const url of extraUrls) {
    if (isGifUrl(url)) {
      urls.add(url);
    }
  }

  const map = new Map();
  const urlList = Array.from(urls);
  const total = Math.max(1, urlList.length);
  for (let index = 0; index < urlList.length; index += 1) {
    const url = urlList[index];
    throwIfTaskCancelled(task);
    try {
      const animation = await decodeGifAnimation(url);
      throwIfTaskCancelled(task);
      map.set(url, animation);
    } catch (error) {
      if (isCancellationError(error)) {
        throw error;
      }
      // Skip undecodable GIFs and keep static rendering for those entries.
    }
    if (progress) {
      progress((index + 1) / total);
    }
    await yieldToMainThread(task);
  }

  return map;
}

function getLongestGifAnimationDuration(gifAnimationMap) {
  let longest = 0;
  for (const animation of gifAnimationMap.values()) {
    longest = Math.max(longest, Math.round(Number(animation?.totalDuration) || 0));
  }
  return longest;
}

function getBackgroundAnimationDuration(options = {}) {
  return Math.max(0, Math.round(Number(options.backgroundImageAnimation?.totalDuration) || 0));
}

function getNativeGifFrameDelaysForCount(gifAnimationMap, frameCountOverride) {
  const targetFrameCount = Math.floor(Number(frameCountOverride));
  if (!Number.isFinite(targetFrameCount) || targetFrameCount <= 0) {
    return null;
  }

  let matchedDurations = null;
  let matchedTotalDuration = 0;
  for (const animation of gifAnimationMap.values()) {
    const frames = Array.isArray(animation?.frames) ? animation.frames : [];
    const durations = Array.isArray(animation?.durations) ? animation.durations : [];
    if (frames.length !== targetFrameCount || durations.length !== targetFrameCount) {
      continue;
    }

    const normalizedDurations = durations.map((duration) =>
      Math.max(20, Math.round(Number(duration) || EXPORT_GIF_FRAME_DELAY_MS))
    );
    const totalDuration = normalizedDurations.reduce((sum, duration) => sum + duration, 0);
    if (!matchedDurations || totalDuration > matchedTotalDuration) {
      matchedDurations = normalizedDurations;
      matchedTotalDuration = totalDuration;
    }
  }

  return matchedDurations;
}

function createExportFrameDelays(durationMs, frameCountOverride = null) {
  if (Number.isFinite(Number(frameCountOverride)) && Number(frameCountOverride) > 0) {
    return Array.from(
      { length: clamp(Math.floor(Number(frameCountOverride)), 1, EXPORT_MAX_FRAME_COUNT) },
      () => EXPORT_GIF_FRAME_DELAY_MS
    );
  }

  const duration = Math.max(EXPORT_GIF_FRAME_DELAY_MS, Math.round(Number(durationMs) || EXPORT_GIF_DURATION_MS));
  const frameCount = clamp(Math.ceil(duration / EXPORT_GIF_FRAME_DELAY_MS), 1, EXPORT_MAX_FRAME_COUNT);
  if (frameCount === 1) {
    return [duration];
  }

  const delays = Array.from({ length: frameCount }, () => EXPORT_GIF_FRAME_DELAY_MS);
  const finalDelay = duration - EXPORT_GIF_FRAME_DELAY_MS * (frameCount - 1);
  if (finalDelay >= 20) {
    delays[delays.length - 1] = finalDelay;
  } else {
    delays[delays.length - 2] += finalDelay;
    delays.pop();
  }
  return delays;
}

function getExportGifFrameDelays(gifAnimationMap, options = {}) {
  const frameCountOverride = Number(options.frameCountOverride);
  if (Number.isFinite(frameCountOverride) && frameCountOverride > 0) {
    const nativeFrameDelays = getNativeGifFrameDelaysForCount(gifAnimationMap, frameCountOverride);
    if (nativeFrameDelays) {
      return nativeFrameDelays;
    }
    return createExportFrameDelays(0, frameCountOverride);
  }

  if (options.animationAuto !== false) {
    const longestDuration = Math.max(
      getLongestGifAnimationDuration(gifAnimationMap),
      getBackgroundAnimationDuration(options)
    );
    return createExportFrameDelays(longestDuration || EXPORT_GIF_DURATION_MS);
  }

  const manualSeconds = EXPORT_MANUAL_SECONDS_PRESETS.includes(Number(options.animationSeconds))
    ? Number(options.animationSeconds)
    : 1;
  return createExportFrameDelays(manualSeconds * 1000);
}

function getExportVideoDurationMs(gifAnimationMap, options = {}) {
  if (options.videoAuto !== false) {
    return Math.max(
      100,
      Math.max(getLongestGifAnimationDuration(gifAnimationMap), getBackgroundAnimationDuration(options)) ||
        EXPORT_GIF_DURATION_MS
    );
  }
  return Math.max(
    100,
    Math.round(clamp(Number(options.videoSeconds) || 0, 0, EXPORT_VIDEO_MAX_SECONDS) * 1000)
  );
}

function getVideoScaledResolution(resolution) {
  const width = Math.max(1, Math.round(Number(resolution?.width) || 1));
  const height = Math.max(1, Math.round(Number(resolution?.height) || 1));
  const multiplier = Math.min(
    1,
    EXPORT_VIDEO_MAX_DIMENSION / width,
    EXPORT_VIDEO_MAX_DIMENSION / height
  );
  return {
    width: Math.max(1, Math.round(width * multiplier)),
    height: Math.max(1, Math.round(height * multiplier))
  };
}

function getSupportedVideoMimeType() {
  if (typeof MediaRecorder !== "function" || typeof MediaRecorder.isTypeSupported !== "function") {
    return "";
  }
  return [
    "video/mp4;codecs=avc1.42E01E",
    "video/mp4;codecs=h264",
    "video/mp4",
    "video/webm;codecs=vp9",
    "video/webm;codecs=vp8",
    "video/webm"
  ].find((type) => MediaRecorder.isTypeSupported(type)) || "";
}

function getVideoExtensionForMimeType(mimeType) {
  return String(mimeType || "").startsWith("video/mp4") ? "mp4" : "webm";
}

function loadExportBackgroundImageElement(url) {
  if (!url) {
    return Promise.resolve(null);
  }
  if (!exportBackgroundImageCache.has(url)) {
    exportBackgroundImageCache.set(
      url,
      new Promise((resolve, reject) => {
        const image = new Image();
        image.onload = () => resolve(image);
        image.onerror = () => reject(new Error("Could not load export background image."));
        image.src = url;
      }).catch((error) => {
        exportBackgroundImageCache.delete(url);
        throw error;
      })
    );
  }
  return exportBackgroundImageCache.get(url);
}

function loadExportBackgroundAnimation(url) {
  if (!isGifUrl(url)) {
    return Promise.resolve(null);
  }
  if (!exportBackgroundAnimationCache.has(url)) {
    exportBackgroundAnimationCache.set(
      url,
      decodeGifAnimation(url).catch((error) => {
        exportBackgroundAnimationCache.delete(url);
        throw error;
      })
    );
  }
  return exportBackgroundAnimationCache.get(url);
}

async function getExportBackgroundImageOptions() {
  const imageUrl = typeof state.exportBgImageUrl === "string" ? state.exportBgImageUrl : "";
  if (!imageUrl || state.exportBackgroundEnabled === false) {
    return {};
  }

  try {
    const [image, animation] = await Promise.all([
      loadExportBackgroundImageElement(imageUrl),
      loadExportBackgroundAnimation(imageUrl).catch(() => null)
    ]);
    if (!image) {
      return {};
    }
    return {
      backgroundImageElement: image,
      backgroundImageAnimation: animation,
      backgroundImageOpacity: clamp(Number(state.exportBgImageOpacity) || 0, 0, 100) / 100,
      backgroundImageMode: state.exportBgImageMode === "tile" ? "tile" : "stretch",
      backgroundImageTileSize: normalizeExportBgTileSize(state.exportBgImageTileSize)
    };
  } catch (error) {
    return {};
  }
}

function drawExportBackgroundImage(ctx, selectionBounds, outputWidth, outputHeight, options = {}) {
  const animatedFrame = resolveGifFrameSource(options.backgroundImageAnimation, options.backgroundImageTimeMs || 0);
  const image = animatedFrame || options.backgroundImageElement;
  if (!image || (!(image instanceof HTMLCanvasElement) && (!(image instanceof HTMLImageElement) || !image.complete))) {
    return;
  }

  const opacity = clamp(Number(options.backgroundImageOpacity), 0, 1);
  if (opacity <= 0) {
    return;
  }

  const naturalWidth = Math.max(1, image.naturalWidth || image.width || 1);
  const naturalHeight = Math.max(1, image.naturalHeight || image.height || 1);

  ctx.save();
  ctx.globalAlpha = opacity;
  ctx.imageSmoothingEnabled = true;
  if (options.backgroundImageMode === "tile") {
    const selectionWidth = Math.max(1, selectionBounds.right - selectionBounds.left);
    const scaleX = outputWidth / selectionWidth;
    const tileWidth = Math.max(1, normalizeExportBgTileSize(options.backgroundImageTileSize) * scaleX);
    const tileHeight = Math.max(1, tileWidth * (naturalHeight / naturalWidth));
    const startX = -(outputWidth % tileWidth) / 2;
    const startY = -(outputHeight % tileHeight) / 2;
    for (let y = startY; y < outputHeight; y += tileHeight) {
      for (let x = startX; x < outputWidth; x += tileWidth) {
        ctx.drawImage(image, x, y, tileWidth, tileHeight);
      }
    }
  } else {
    const scale = Math.max(outputWidth / naturalWidth, outputHeight / naturalHeight);
    const drawWidth = naturalWidth * scale;
    const drawHeight = naturalHeight * scale;
    ctx.drawImage(
      image,
      (outputWidth - drawWidth) / 2,
      (outputHeight - drawHeight) / 2,
      drawWidth,
      drawHeight
    );
  }
  ctx.restore();
}

function getStaticExportBackgroundCanvas(selectionBounds, outputWidth, outputHeight, options = {}) {
  if (options.backgroundImageAnimation) {
    return null;
  }
  const image = options.backgroundImageElement;
  if (!(image instanceof HTMLImageElement) || !image.complete) {
    return null;
  }
  const key = [
    outputWidth,
    outputHeight,
    Math.round((selectionBounds.right - selectionBounds.left) * 100) / 100,
    Math.round((selectionBounds.bottom - selectionBounds.top) * 100) / 100,
    options.backgroundImageMode === "tile" ? "tile" : "stretch",
    normalizeExportBgTileSize(options.backgroundImageTileSize),
    clamp(Number(options.backgroundImageOpacity), 0, 1),
    image.currentSrc || image.src || ""
  ].join("|");
  if (exportBackgroundRenderCache.has(key)) {
    return exportBackgroundRenderCache.get(key);
  }
  const canvas = document.createElement("canvas");
  canvas.width = outputWidth;
  canvas.height = outputHeight;
  const cacheCtx = canvas.getContext("2d", { alpha: true });
  if (!cacheCtx) {
    return null;
  }
  drawExportBackgroundImage(cacheCtx, selectionBounds, outputWidth, outputHeight, options);
  if (exportBackgroundRenderCache.size > 6) {
    exportBackgroundRenderCache.clear();
  }
  exportBackgroundRenderCache.set(key, canvas);
  return canvas;
}

function prepareExportFrame(
  ctx,
  selectionBounds,
  outputWidth,
  outputHeight,
  options = {}
) {
  const includeBackground = options.includeBackground !== false;
  const backgroundColor = normalizeHexColor(options.backgroundColor, "#ffffff");
  const matteColor = typeof options.matteColor === "string" ? options.matteColor : "";
  const selectionWidth = Math.max(1, selectionBounds.right - selectionBounds.left);
  const selectionHeight = Math.max(1, selectionBounds.bottom - selectionBounds.top);
  const scaleX = outputWidth / selectionWidth;
  const scaleY = outputHeight / selectionHeight;

  ctx.clearRect(0, 0, outputWidth, outputHeight);
  if (includeBackground || matteColor) {
    ctx.save();
    ctx.globalAlpha = 1;
    ctx.fillStyle = includeBackground ? backgroundColor : matteColor;
    ctx.fillRect(0, 0, outputWidth, outputHeight);
    ctx.restore();
  }
  const staticBackgroundCanvas = getStaticExportBackgroundCanvas(selectionBounds, outputWidth, outputHeight, options);
  if (staticBackgroundCanvas) {
    ctx.drawImage(staticBackgroundCanvas, 0, 0);
  } else {
    drawExportBackgroundImage(ctx, selectionBounds, outputWidth, outputHeight, options);
  }

  return { scaleX, scaleY };
}

function drawExportImageWithTint(ctx, frameSource, drawWidth, drawHeight, imageRendering, tintSettings) {
  const tintLayers = getTintLayerList(tintSettings);
  if (!tintLayers.length) {
    ctx.drawImage(frameSource, -drawWidth / 2, -drawHeight / 2, drawWidth, drawHeight);
    return;
  }

  const scratchWidth = Math.max(1, Math.ceil(drawWidth));
  const scratchHeight = Math.max(1, Math.ceil(drawHeight));
  if (!exportTintScratchCanvas) {
    exportTintScratchCanvas = document.createElement("canvas");
  }
  if (exportTintScratchCanvas.width !== scratchWidth) {
    exportTintScratchCanvas.width = scratchWidth;
  }
  if (exportTintScratchCanvas.height !== scratchHeight) {
    exportTintScratchCanvas.height = scratchHeight;
  }

  const scratchCtx = exportTintScratchCanvas.getContext("2d", { alpha: true });
  if (!scratchCtx) {
    ctx.drawImage(frameSource, -drawWidth / 2, -drawHeight / 2, drawWidth, drawHeight);
    return;
  }

  scratchCtx.clearRect(0, 0, scratchWidth, scratchHeight);
  scratchCtx.globalAlpha = 1;
  scratchCtx.globalCompositeOperation = "source-over";
  scratchCtx.imageSmoothingEnabled = imageRendering === "auto";
  scratchCtx.drawImage(frameSource, 0, 0, scratchWidth, scratchHeight);
  for (const tintLayer of tintLayers) {
    scratchCtx.globalCompositeOperation = "source-atop";
    scratchCtx.globalAlpha = tintLayer.amountPercent / 100;
    scratchCtx.fillStyle = tintLayer.color;
    scratchCtx.fillRect(0, 0, scratchWidth, scratchHeight);
  }
  scratchCtx.globalAlpha = 1;
  scratchCtx.globalCompositeOperation = "source-over";

  ctx.drawImage(exportTintScratchCanvas, -drawWidth / 2, -drawHeight / 2, drawWidth, drawHeight);
}

function drawExportStampEntry(ctx, selectionBounds, scaleX, scaleY, entry, gifAnimationMap = null, timeMs = 0) {
  let frameSource = entry.element;
  if (gifAnimationMap && isGifUrl(entry.sourceUrl)) {
    const animation = gifAnimationMap.get(entry.sourceUrl);
    const animatedSource = resolveGifFrameSource(animation, timeMs);
    if (animatedSource) {
      frameSource = animatedSource;
    }
  }

  const drawWidth = entry.width * scaleX;
  const drawHeight = entry.height * scaleY;
  const drawCenterX = (entry.centerX - selectionBounds.left) * scaleX;
  const drawCenterY = (entry.centerY - selectionBounds.top) * scaleY;

  ctx.save();
  ctx.globalAlpha = entry.opacity;
  ctx.imageSmoothingEnabled = entry.imageRendering === "auto";
  ctx.translate(drawCenterX, drawCenterY);
  ctx.rotate((entry.rotation * Math.PI) / 180);
  drawExportImageWithTint(ctx, frameSource, drawWidth, drawHeight, entry.imageRendering, entry.tintSettings);
  ctx.restore();
}

function drawExportFrame(
  ctx,
  selectionBounds,
  outputWidth,
  outputHeight,
  entries,
  gifAnimationMap = null,
  timeMs = 0,
  options = {}
) {
  if (Number.isFinite(Number(options.sequenceTimeMs))) {
    runLayerSequences(Number(options.sequenceTimeMs));
    refreshExportSequenceEntries(entries, selectionBounds, Number(options.sequenceTimeMs));
  }
  const { scaleX, scaleY } = prepareExportFrame(
    ctx,
    selectionBounds,
    outputWidth,
    outputHeight,
    { ...options, backgroundImageTimeMs: timeMs }
  );
  for (const entry of entries) {
    drawExportStampEntry(ctx, selectionBounds, scaleX, scaleY, entry, gifAnimationMap, timeMs);
  }
}

async function drawExportFrameAsync(
  ctx,
  selectionBounds,
  outputWidth,
  outputHeight,
  entries,
  gifAnimationMap = null,
  timeMs = 0,
  options = {},
  task = null,
  progress = null
) {
  if (Number.isFinite(Number(options.sequenceTimeMs))) {
    runLayerSequences(Number(options.sequenceTimeMs));
    refreshExportSequenceEntries(entries, selectionBounds, Number(options.sequenceTimeMs));
  }
  const { scaleX, scaleY } = prepareExportFrame(
    ctx,
    selectionBounds,
    outputWidth,
    outputHeight,
    { ...options, backgroundImageTimeMs: timeMs }
  );
  const total = Math.max(1, entries.length);
  for (let index = 0; index < entries.length; index += 1) {
    throwIfTaskCancelled(task);
    drawExportStampEntry(ctx, selectionBounds, scaleX, scaleY, entries[index], gifAnimationMap, timeMs);
    if (progress && (index === entries.length - 1 || index % EXPORT_CANCEL_CHECK_INTERVAL === 0)) {
      progress((index + 1) / total);
    }
    if (index > 0 && index % EXPORT_CANCEL_CHECK_INTERVAL === 0) {
      await yieldToMainThread(task);
    }
  }
}

function canvasToPngBlob(canvas) {
  return new Promise((resolve, reject) => {
    canvas.toBlob((blob) => {
      if (!blob) {
        reject(new Error("Failed to create PNG export."));
        return;
      }
      resolve(blob);
    }, "image/png");
  });
}

function createTransparentGifFrameImageData(ctx, width, height) {
  const imageData = ctx.getImageData(0, 0, width, height);
  const data = imageData.data;
  let hasTransparentPixel = false;
  for (let index = 0; index < data.length; index += 4) {
    if (data[index + 3] < 128) {
      data[index] = 0;
      data[index + 1] = 255;
      data[index + 2] = 1;
      hasTransparentPixel = true;
    }
    data[index + 3] = 255;
  }
  if (!hasTransparentPixel && data.length >= 4) {
    data[0] = 0;
    data[1] = 255;
    data[2] = 1;
  }
  return imageData;
}

async function renderExportPngBlob(selectionBounds, outputWidth, outputHeight, entries, options = {}, task = null) {
  const canvas = document.createElement("canvas");
  canvas.width = outputWidth;
  canvas.height = outputHeight;
  const ctx = canvas.getContext("2d", { alpha: true });
  if (!ctx) {
    throw new Error("Could not create export canvas.");
  }
  await drawExportFrameAsync(
    ctx,
    selectionBounds,
    outputWidth,
    outputHeight,
    entries,
    null,
    0,
    { ...options, sequenceTimeMs: options.sequenceExportActive ? 0 : null },
    task,
    (ratio) => updateExportProgress(
      task,
      EXPORT_PROGRESS_COLLECT_END + (EXPORT_PROGRESS_DRAW_END - EXPORT_PROGRESS_COLLECT_END) * ratio,
      "Drawing"
    )
  );
  throwIfTaskCancelled(task);
  updateExportProgress(task, EXPORT_PROGRESS_PNG_ENCODE_HOLD, "Encoding");
  return canvasToPngBlob(canvas);
}

async function renderExportGifBlob(selectionBounds, outputWidth, outputHeight, entries, options = {}, task = null) {
  await loadGifLibrary();
  throwIfTaskCancelled(task);
  if (typeof window.GIF !== "function") {
    throw new Error("GIF encoder is unavailable.");
  }

  const includeBackground = options.includeBackground !== false;
  const backgroundColor = normalizeHexColor(options.backgroundColor, "#ffffff");
  const frameOptions = {
    ...options,
    includeBackground,
    matteColor: ""
  };
  const frameCanvas = document.createElement("canvas");
  frameCanvas.width = outputWidth;
  frameCanvas.height = outputHeight;
  const frameCtx = frameCanvas.getContext("2d", { alpha: !includeBackground });
  if (!frameCtx) {
    throw new Error("Could not create GIF frame canvas.");
  }
  if (includeBackground) {
    frameCtx.globalCompositeOperation = "copy";
    frameCtx.fillStyle = backgroundColor;
    frameCtx.fillRect(0, 0, outputWidth, outputHeight);
    frameCtx.globalCompositeOperation = "source-over";
  }
  const gifAnimationMap = await buildGifAnimationMap(
    entries,
    task,
    (ratio) => updateExportProgress(
      task,
      EXPORT_PROGRESS_COLLECT_END + (EXPORT_PROGRESS_DECODE_END - EXPORT_PROGRESS_COLLECT_END) * ratio,
      "Decoding"
    ),
    getSequenceExportSourceUrls()
  );
  throwIfTaskCancelled(task);
  const frameDelays = getExportGifFrameDelays(gifAnimationMap, options);

  const gif = new window.GIF({
    workers: 2,
    quality: 1,
    width: outputWidth,
    height: outputHeight,
    repeat: 0,
    dither: false,
    background: includeBackground ? backgroundColor : GIF_TRANSPARENT_MATTE,
    globalPalette: includeBackground ? true : false,
    workerScript: GIF_JS_WORKER_URL,
    ...(includeBackground ? {} : { transparent: GIF_TRANSPARENT_MATTE_HEX })
  });
  if (task) {
    task.gif = gif;
  }

  let elapsedMs = 0;
  for (let index = 0; index < frameDelays.length; index += 1) {
    throwIfTaskCancelled(task);
    const frameStartRatio = index / Math.max(1, frameDelays.length);
    const frameEndRatio = (index + 1) / Math.max(1, frameDelays.length);
    await drawExportFrameAsync(
      frameCtx,
      selectionBounds,
      outputWidth,
      outputHeight,
      entries,
      gifAnimationMap,
      elapsedMs,
      { ...frameOptions, sequenceTimeMs: options.sequenceExportActive ? elapsedMs : null },
      task,
      (entryRatio) => updateExportProgress(
        task,
        EXPORT_PROGRESS_DECODE_END +
          (EXPORT_PROGRESS_DRAW_END - EXPORT_PROGRESS_DECODE_END) *
            (frameStartRatio + (frameEndRatio - frameStartRatio) * entryRatio),
        "Drawing"
      )
    );
    if (includeBackground) {
      gif.addFrame(frameCanvas, {
        copy: true,
        delay: frameDelays[index],
        dispose: 2
      });
    } else {
      gif.addFrame(createTransparentGifFrameImageData(frameCtx, outputWidth, outputHeight), {
        delay: frameDelays[index],
        dispose: 2
      });
    }
    elapsedMs += frameDelays[index];
  }

  return new Promise((resolve, reject) => {
    const clearGifTask = () => {
      if (task && task.gif === gif) {
        task.gif = null;
      }
    };
    gif.on("progress", (ratio) => {
      updateExportProgress(
        task,
        EXPORT_PROGRESS_DRAW_END + (EXPORT_PROGRESS_ENCODE_END - EXPORT_PROGRESS_DRAW_END) * ratio,
        "Encoding"
      );
    });
    gif.on("finished", (blob) => {
      clearGifTask();
      if (task && task.cancelled) {
        reject(createCancellationError());
        return;
      }
      resolve(blob);
    });
    gif.on("abort", () => {
      clearGifTask();
      reject(createCancellationError());
    });
    throwIfTaskCancelled(task);
    gif.render();
  });
}

async function renderExportVideoBlob(selectionBounds, outputWidth, outputHeight, entries, options = {}, task = null) {
  const mimeType = getSupportedVideoMimeType();
  if (!mimeType) {
    throw new Error("Video encoding is unavailable in this browser.");
  }

  const recordCanvas = document.createElement("canvas");
  recordCanvas.width = outputWidth;
  recordCanvas.height = outputHeight;
  const recordCtx = recordCanvas.getContext("2d", { alpha: options.includeBackground === false });
  const renderCanvas = document.createElement("canvas");
  renderCanvas.width = outputWidth;
  renderCanvas.height = outputHeight;
  const renderCtx = renderCanvas.getContext("2d", { alpha: options.includeBackground === false });
  if (!recordCtx || !renderCtx || typeof recordCanvas.captureStream !== "function") {
    throw new Error("Could not create video export canvas.");
  }

  const stream = recordCanvas.captureStream(EXPORT_VIDEO_FPS);
  const chunks = [];
  const recorder = new MediaRecorder(stream, {
    mimeType,
    videoBitsPerSecond: Math.max(2500000, Math.min(12000000, outputWidth * outputHeight * 8))
  });
  task.mediaRecorder = recorder;

  const recordedBlobPromise = new Promise((resolve, reject) => {
    recorder.ondataavailable = (event) => {
      if (event.data && event.data.size > 0) {
        chunks.push(event.data);
      }
    };
    recorder.onerror = () => reject(recorder.error || new Error("Video export failed."));
    recorder.onstop = () => {
      if (task && task.cancelled) {
        reject(createCancellationError());
        return;
      }
      resolve(new Blob(chunks, { type: mimeType }));
    };
  });

  const gifAnimationMap = await buildGifAnimationMap(
    entries,
    task,
    (ratio) => updateExportProgress(
      task,
      EXPORT_PROGRESS_COLLECT_END + (EXPORT_PROGRESS_DECODE_END - EXPORT_PROGRESS_COLLECT_END) * ratio,
      "Decoding"
    ),
    getSequenceExportSourceUrls()
  );
  throwIfTaskCancelled(task);

  const durationMs = getExportVideoDurationMs(gifAnimationMap, options);
  const frameIntervalMs = 1000 / EXPORT_VIDEO_FPS;
  const frameOptions = {
    ...options,
    includeBackground: options.includeBackground !== false
  };

  await drawExportFrameAsync(
    renderCtx,
    selectionBounds,
    outputWidth,
    outputHeight,
    entries,
    gifAnimationMap,
    0,
    { ...frameOptions, sequenceTimeMs: options.sequenceExportActive ? 0 : null },
    task
  );
  recordCtx.clearRect(0, 0, outputWidth, outputHeight);
  recordCtx.drawImage(renderCanvas, 0, 0);

  const recordingStartTime = performance.now();
  recorder.start();
  await yieldToMainThread(task);
  try {
    const recordingEndTime = recordingStartTime + durationMs;
    let nextFrameTargetTime = recordingStartTime;
    let estimatedRenderMs = frameIntervalMs;

    while (true) {
      throwIfTaskCancelled(task);
      const now = performance.now();
      const elapsedMs = Math.max(0, now - recordingStartTime);
      const remainingMs = recordingEndTime - now;
      if (elapsedMs >= durationMs || remainingMs <= 0) {
        break;
      }

      if (remainingMs < Math.min(frameIntervalMs, Math.max(4, estimatedRenderMs * 1.1))) {
        await waitForExportFrameDelay(remainingMs, task);
        break;
      }

      const frameTimeMs = Math.min(durationMs, elapsedMs);
      const renderStartTime = performance.now();
      drawExportFrame(
        renderCtx,
        selectionBounds,
        outputWidth,
        outputHeight,
        entries,
        gifAnimationMap,
        frameTimeMs,
        { ...frameOptions, sequenceTimeMs: options.sequenceExportActive ? frameTimeMs : null }
      );
      recordCtx.clearRect(0, 0, outputWidth, outputHeight);
      recordCtx.drawImage(renderCanvas, 0, 0);

      const renderElapsedMs = Math.max(0, performance.now() - renderStartTime);
      estimatedRenderMs = estimatedRenderMs * 0.8 + renderElapsedMs * 0.2;
      const elapsedAfterRenderMs = clamp(performance.now() - recordingStartTime, 0, durationMs);
      updateExportProgress(
        task,
        EXPORT_PROGRESS_DECODE_END +
          (EXPORT_PROGRESS_ENCODE_END - EXPORT_PROGRESS_DECODE_END) *
            (elapsedAfterRenderMs / Math.max(1, durationMs)),
        "Rendering"
      );

      while (nextFrameTargetTime <= performance.now()) {
        nextFrameTargetTime += frameIntervalMs;
      }
      const delayMs = Math.min(
        recordingEndTime - performance.now(),
        Math.max(0, nextFrameTargetTime - performance.now())
      );
      if (delayMs > 0) {
        await waitForExportFrameDelay(delayMs, task);
      } else {
        await yieldToMainThread(task);
      }
    }

    const finalDelayMs = recordingEndTime - performance.now();
    if (finalDelayMs > 0) {
      await waitForExportFrameDelay(finalDelayMs, task);
    }
    updateExportProgress(task, EXPORT_PROGRESS_ENCODE_END, "Encoding");
    throwIfTaskCancelled(task);
    recorder.stop();
    return await recordedBlobPromise;
  } finally {
    if (recorder.state !== "inactive") {
      try {
        recorder.stop();
      } catch (error) {
        // Recorder may already be stopping after cancellation.
      }
      recordedBlobPromise.catch(() => {});
    }
    for (const mediaTrack of stream.getTracks()) {
      mediaTrack.stop();
    }
    if (task && task.mediaRecorder === recorder) {
      task.mediaRecorder = null;
    }
  }
}

function downloadBlob(blob, filename) {
  const objectUrl = URL.createObjectURL(blob);
  const anchor = document.createElement("a");
  anchor.href = objectUrl;
  anchor.download = filename;
  document.body.appendChild(anchor);
  anchor.click();
  anchor.remove();
  window.setTimeout(() => URL.revokeObjectURL(objectUrl), 1000);
}

async function confirmExport() {
  if (!state.exportMode || !state.exportSelectionBounds || state.exportTask) {
    return;
  }

  const task = createCancellableTask("export");
  task.button = exportButton;
  const normalized = normalizeExportSelectionBounds(state.exportSelectionBounds);
  const resolution = getExportScaledResolution(normalized);
  state.exportTask = task;
  updateExportModeUI();
  restoreAllCulledStampSources();
  updateBrushCursorPreview();
  const timestamp = Date.now();
  const exportOptions = {
    includeBackground: Boolean(state.exportBackgroundEnabled),
    backgroundColor: state.canvasBackgroundColor,
    animationAuto: state.exportAnimationAuto !== false,
    animationSeconds: state.exportAnimationSeconds,
    frameCountOverride: state.exportAnimationAuto === false ? getExportFrameCountOverride() : null,
    sequenceExportActive: hasActiveSequenceEffectOnCanvas()
  };
  const sequenceSnapshot = exportOptions.sequenceExportActive ? createSequenceExportSnapshot() : null;

  exportButton.disabled = true;
  exportCancelButton.disabled = false;
  exportButton.classList.add("is-loading");
  updateExportProgress(task, 0, "Exporting");
  updateBrushStatus("Exporting... Press Esc to cancel.");
  try {
    Object.assign(exportOptions, await getExportBackgroundImageOptions());
    throwIfTaskCancelled(task);
    if (sequenceSnapshot) {
      state.sequenceExportActive = true;
      resetSequencesForExport();
    }
    const entries = await collectExportStampEntries(
      normalized,
      task,
      (ratio) => updateExportProgress(task, EXPORT_PROGRESS_COLLECT_END * ratio, "Collecting")
    );
    throwIfTaskCancelled(task);
    const hasGif = hasGifStampOnCanvas() || exportOptions.sequenceExportActive;
    const blob = hasGif
      ? await renderExportGifBlob(normalized, resolution.width, resolution.height, entries, exportOptions, task)
      : await renderExportPngBlob(normalized, resolution.width, resolution.height, entries, exportOptions, task);
    throwIfTaskCancelled(task);
    const extension = hasGif ? "gif" : "png";

    const filename = `image-draw-export-${timestamp}.${extension}`;
    updateExportProgress(task, 100, "Done");
    downloadBlob(blob, filename);
    state.exportTask = null;
    exitExportMode();
    setSidebarTab("draw");
    updateBrushStatus();
  } catch (error) {
    if (isCancellationError(error)) {
      updateBrushStatus("Export cancelled.");
    } else {
      updateBrushStatus("Could not complete export.");
    }
    resetExportProgress();
    exportButton.setAttribute("aria-label", "Render GIF");
    exportButton.title = "Render GIF";
    exportButton.disabled = false;
    exportCancelButton.disabled = true;
  } finally {
    if (sequenceSnapshot) {
      restoreSequenceExportSnapshot(sequenceSnapshot);
      state.sequenceExportActive = false;
    }
    if (state.exportTask === task) {
      state.exportTask = null;
    }
    exportButton.classList.remove("is-loading");
    resetExportProgress(exportButton, "Render GIF");
    updateUndoState();
    updateExportModeUI();
    scheduleStampVisibilityRefresh();
  }
}

async function confirmVideoExport() {
  if (!state.exportMode || !state.exportSelectionBounds || state.exportTask || !exportVideoButton) {
    return;
  }

  const mimeType = getSupportedVideoMimeType();
  if (!mimeType) {
    updateBrushStatus("Video export is not supported in this browser.");
    return;
  }

  const task = createCancellableTask("video-export");
  task.button = exportVideoButton;
  const normalized = normalizeExportSelectionBounds(state.exportSelectionBounds);
  const resolution = getVideoScaledResolution(getExportScaledResolution(normalized));
  state.exportTask = task;
  updateExportModeUI();
  restoreAllCulledStampSources();
  updateBrushCursorPreview();
  const timestamp = Date.now();
  const exportOptions = {
    includeBackground: Boolean(state.exportBackgroundEnabled),
    backgroundColor: state.canvasBackgroundColor,
    videoAuto: state.exportVideoAuto !== false,
    videoSeconds: state.exportVideoSeconds,
    sequenceExportActive: hasActiveSequenceEffectOnCanvas()
  };
  const sequenceSnapshot = exportOptions.sequenceExportActive ? createSequenceExportSnapshot() : null;

  exportVideoButton.disabled = true;
  if (exportVideoCancelButton) {
    exportVideoCancelButton.disabled = false;
  }
  exportVideoButton.classList.add("is-loading");
  updateExportProgress(task, 0, "Exporting");
  updateBrushStatus("Exporting video... Press Esc to cancel.");
  try {
    Object.assign(exportOptions, await getExportBackgroundImageOptions());
    throwIfTaskCancelled(task);
    if (sequenceSnapshot) {
      state.sequenceExportActive = true;
      resetSequencesForExport();
    }
    const entries = await collectExportStampEntries(
      normalized,
      task,
      (ratio) => updateExportProgress(task, EXPORT_PROGRESS_COLLECT_END * ratio, "Collecting")
    );
    throwIfTaskCancelled(task);
    const blob = await renderExportVideoBlob(
      normalized,
      resolution.width,
      resolution.height,
      entries,
      exportOptions,
      task
    );
    throwIfTaskCancelled(task);
    const extension = getVideoExtensionForMimeType(mimeType);
    const filename = `image-draw-export-${timestamp}.${extension}`;
    updateExportProgress(task, 100, "Done");
    downloadBlob(blob, filename);
    state.exportTask = null;
    exitExportMode();
    setSidebarTab("draw");
    if (extension === "mp4") {
      updateBrushStatus();
    } else {
      updateBrushStatus("Video exported as WebM; MP4 is not supported in this browser.");
    }
  } catch (error) {
    if (isCancellationError(error)) {
      updateBrushStatus("Video export cancelled.");
    } else {
      updateBrushStatus("Could not complete video export.");
    }
    resetExportProgress(exportVideoButton, "Render Video");
    exportVideoButton.setAttribute("aria-label", "Render Video");
    exportVideoButton.title = "Render Video";
    exportVideoButton.disabled = false;
    if (exportVideoCancelButton) {
      exportVideoCancelButton.disabled = true;
    }
  } finally {
    if (sequenceSnapshot) {
      restoreSequenceExportSnapshot(sequenceSnapshot);
      state.sequenceExportActive = false;
    }
    if (state.exportTask === task) {
      state.exportTask = null;
    }
    exportVideoButton.classList.remove("is-loading");
    resetExportProgress(exportVideoButton, "Render Video");
    updateUndoState();
    updateExportModeUI();
    scheduleStampVisibilityRefresh();
  }
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

async function mapWithConcurrency(items, limit, mapper) {
  const results = new Array(items.length);
  let nextIndex = 0;
  const workerCount = Math.min(Math.max(1, limit), items.length);
  const workers = Array.from({ length: workerCount }, async () => {
    while (nextIndex < items.length) {
      const currentIndex = nextIndex;
      nextIndex += 1;
      results[currentIndex] = await mapper(items[currentIndex], currentIndex);
    }
  });
  await Promise.all(workers);
  return results;
}

function isAllowedImage(file) {
  if (!file || !file.name) {
    return false;
  }
  return ALLOWED_EXTENSIONS.test(file.name);
}

async function loadStockBrushFolder(folderId) {
  if (state.stockBrushLoadingFolderId) {
    return;
  }

  const folder = getStockBrushFolderById(folderId);
  const files = getStockBrushFiles(folder);
  if (!folder || !files.length) {
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.favoriteReturnState = null;
  clearActiveCustomBrushPreset();
  state.stockBrushLoadingFolderId = folder.id;
  renderStockBrushButtons();
  updateBrushStatus(`Loading ${folder.name} stock brushes...`);

  try {
    const loaded = await loadStockBrushFileData(files);
    if (!loaded.length) {
      updateBrushStatus(`Could not load ${folder.name} stock brushes.`);
      return;
    }

    const previousBrushUrls = state.brushes.map((brush) => brush.url);
    state.brushes = loaded.map((brushData) => {
      const brush = {
        id: state.nextBrushId,
        ...brushData
      };
      state.nextBrushId += 1;
      return brush;
    });
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    state.activeStockBrushFolderId = folder.id;
    clearActiveCustomBrushPreset();
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
    for (const oldUrl of previousBrushUrls) {
      maybeReleaseObjectUrl(oldUrl);
    }
    if (state.eraseMode) {
      setEraseMode(false);
    }

    brushInput.value = "";
    updateBrushStatus();
    renderBrushGallery();
    updateEraseCursorGeometry();
    updateBrushCursorPreview();
    scheduleSessionSave();
  } finally {
    state.stockBrushLoadingFolderId = null;
    renderStockBrushButtons();
  }
}

async function loadStockBrushFileData(files) {
  const uniqueFiles = Array.from(new Set(files));
  return loadBrushSourceData(uniqueFiles.map((filePath) => encodeStockBrushPath(filePath)));
}

function cloneBrushSourceData(brushData) {
  return {
    ...brushData,
    frameRange: brushData?.frameRange ? { ...brushData.frameRange } : null,
    cropRect: brushData?.cropRect ? { ...brushData.cropRect } : null
  };
}

function getBrushSourceFileName(sourceUrl) {
  const cleanUrl = String(sourceUrl || "").split(/[?#]/)[0];
  if (cleanUrl.startsWith("data:")) {
    return "favorite brush";
  }
  const parts = cleanUrl.split("/");
  const encodedName = parts[parts.length - 1] || "brush";
  try {
    return decodeURIComponent(encodedName);
  } catch (error) {
    return encodedName;
  }
}

async function loadBrushSourceData(sources) {
  const uniqueSources = Array.from(
    new Set(sources.map(normalizeFavoriteBrushSource).filter(Boolean))
  );
  const loadedBrushData = await mapWithConcurrency(uniqueSources, 18, async (sourceUrl) => {
    try {
      if (!brushSourceDataCache.has(sourceUrl)) {
        brushSourceDataCache.set(
          sourceUrl,
          getImageDimensions(sourceUrl)
            .then((dimensions) => ({
              url: sourceUrl,
              name: getBrushSourceFileName(sourceUrl),
              width: dimensions.width,
              height: dimensions.height,
              originalUrl: sourceUrl,
              originalWidth: dimensions.width,
              originalHeight: dimensions.height,
              frameCount: isGifUrl(sourceUrl) ? null : 1,
              frameRange: null,
              cropRect: null,
              enabled: true,
              weightMode: "normal"
            }))
            .catch((error) => {
              brushSourceDataCache.delete(sourceUrl);
              throw error;
            })
        );
      }
      return cloneBrushSourceData(await brushSourceDataCache.get(sourceUrl));
    } catch (error) {
      return null;
    }
  });
  return loadedBrushData.filter(Boolean);
}

async function loadFavoriteBrushes() {
  if (state.stockBrushLoadingFolderId) {
    return;
  }

  if (state.activeStockBrushFolderId === "favorites" && state.favoriteReturnState) {
    restoreFavoriteReturnState();
    clearActiveCustomBrushPreset();
    return;
  }

  const sources = state.favoriteBrushSources instanceof Set
    ? Array.from(state.favoriteBrushSources).filter(Boolean)
    : [];
  if (!sources.length) {
    updateBrushStatus("No favorite brush data saved.");
    updateFavoriteBrushButtons();
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.stockBrushLoadingFolderId = "favorites";
  clearActiveCustomBrushPreset();
  renderStockBrushButtons();
  updateBrushStatus("Loading favorite brushes...");

  try {
    const loaded = await loadBrushSourceData(sources);
    if (!loaded.length) {
      updateBrushStatus("Could not load favorite brushes.");
      return;
    }

    state.favoriteReturnState = captureFavoriteReturnState();
    state.brushes = loaded.map((brushData) => {
      const brush = {
        id: state.nextBrushId,
        ...brushData
      };
      state.nextBrushId += 1;
      return brush;
    });
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    state.activeStockBrushFolderId = "favorites";
    clearActiveCustomBrushPreset();
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
    if (state.eraseMode) {
      setEraseMode(false);
    }

    brushInput.value = "";
    updateBrushStatus();
    renderBrushGallery();
    updateEraseCursorGeometry();
    updateBrushCursorPreview();
    scheduleSessionSave();
  } finally {
    state.stockBrushLoadingFolderId = null;
    renderStockBrushButtons();
  }
}

async function loadAllStockBrushFolders() {
  if (state.stockBrushLoadingFolderId) {
    return;
  }

  const folders = getOrderedStockBrushFolders().filter((folder) => getStockBrushFiles(folder).length);
  const files = folders.flatMap((folder) => getStockBrushFiles(folder));
  if (!files.length) {
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.favoriteReturnState = null;
  clearActiveCustomBrushPreset();
  state.stockBrushLoadingFolderId = "all";
  renderStockBrushButtons();
  updateBrushStatus("Loading all stock brushes...");

  try {
    const loaded = await loadStockBrushFileData(files);
    if (!loaded.length) {
      updateBrushStatus("Could not load all stock brushes.");
      return;
    }

    const previousBrushUrls = state.brushes.map((brush) => brush.url);
    state.brushes = loaded.map((brushData) => {
      const brush = {
        id: state.nextBrushId,
        ...brushData
      };
      state.nextBrushId += 1;
      return brush;
    });
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    state.activeStockBrushFolderId = "all";
    clearActiveCustomBrushPreset();
    state.brushCursorPreview.brushId = null;
    resetBrushCursorPreviewSource();
    for (const oldUrl of previousBrushUrls) {
      maybeReleaseObjectUrl(oldUrl);
    }
    if (state.eraseMode) {
      setEraseMode(false);
    }

    brushInput.value = "";
    updateBrushStatus();
    renderBrushGallery();
    updateEraseCursorGeometry();
    updateBrushCursorPreview();
    scheduleSessionSave();
  } finally {
    state.stockBrushLoadingFolderId = null;
    renderStockBrushButtons();
  }
}

function unloadBrushDataSelection() {
  if (!state.brushes.length) {
    state.activeStockBrushFolderId = null;
    state.favoriteReturnState = null;
    clearActiveCustomBrushPreset();
    state.soloBrushId = null;
    clearSelectedBrushes();
    if (state.eraseMode) {
      setEraseMode(false);
    }
    updateBrushStatus();
    renderBrushGallery();
    renderStockBrushButtons();
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.favoriteReturnState = null;
  clearActiveCustomBrushPreset();
  const previousBrushUrls = state.brushes.map((brush) => brush.url);
  state.brushes = [];
  clearBrushFrameCountJobs();
  state.soloBrushId = null;
  clearSelectedBrushes();
  state.activeStockBrushFolderId = null;
  clearActiveCustomBrushPreset();
  state.brushCursorPreview.brushId = null;
  resetBrushCursorPreviewSource();
  for (const oldUrl of previousBrushUrls) {
    maybeReleaseObjectUrl(oldUrl);
  }
  if (state.eraseMode) {
    setEraseMode(false);
  }

  brushInput.value = "";
  updateBrushStatus();
  renderBrushGallery();
  renderStockBrushButtons();
  updateEraseCursorGeometry();
  updateBrushCursorPreview();
  scheduleSessionSave();
}

async function loadBrushFiles(files) {
  const validFiles = files.filter(isAllowedImage);
  if (!validFiles.length) {
    updateBrushStatus("No supported image files found.");
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.favoriteReturnState = null;
  clearActiveCustomBrushPreset();
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
        originalUrl: dataUrl,
        originalWidth: dimensions.width,
        originalHeight: dimensions.height,
        frameCount: isGifUrl(dataUrl) || /\.gif$/i.test(file.name) ? null : 1,
        frameRange: null,
        cropRect: null,
        enabled: true,
        weightMode: "normal"
      });
      state.nextBrushId += 1;
    } catch (error) {
      // Skip unreadable files and continue loading the rest.
    }
  }

  state.brushes = loaded;
  clearBrushFrameCountJobs();
  state.soloBrushId = null;
  clearSelectedBrushes();
  state.activeStockBrushFolderId = null;
  clearActiveCustomBrushPreset();
  state.brushCursorPreview.brushId = null;
  resetBrushCursorPreviewSource();
  for (const oldUrl of previousBrushUrls) {
    maybeReleaseObjectUrl(oldUrl);
  }
  if (state.eraseMode) {
    setEraseMode(false);
  }

  if (state.brushes.length) {
    updateBrushStatus();
    renderBrushGallery();
    renderStockBrushButtons();
    updateBrushCursorPreview();
    scheduleSessionSave();
  } else {
    updateBrushStatus("Could not load image data from selection.");
    renderBrushGallery();
    renderStockBrushButtons();
    updateBrushCursorPreview();
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
  const worldOrder = new Map();
  const stamps = world.getElementsByClassName("stamp");
  for (let index = 0; index < stamps.length; index += 1) {
    worldOrder.set(stamps[index], index);
  }
  const removalContext = {
    records: [],
    worldOrder
  };
  const changed = eraseAtPoint(point.x, point.y, radiusWorld, removalContext);

  state.erasing = {
    pointerId: event.pointerId,
    lastX: point.x,
    lastY: point.y,
    changed,
    removalContext,
    pendingX: NaN,
    pendingY: NaN,
    rafId: null
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
  if (erasing.rafId !== null) {
    window.cancelAnimationFrame(erasing.rafId);
    erasing.rafId = null;
  }
  flushPendingErasePoint(erasing);
  const changed = erasing.changed;
  const removals = erasing.removalContext.records;
  state.erasing = null;
  if (changed && removals.length) {
    pushEraseAction(removals);
  }
}

function startDrawing(event) {
  if (!ensureDrawableBrushes()) {
    return;
  }

  const point = screenToWorld(event.clientX, event.clientY);
  const stroke = {
    id: state.nextStrokeId,
    layerNumber: state.nextStrokeId,
    layerType: state.drawMode === "spray" ? "spray" : "stroke",
    brushCategoryName: getActiveBrushCategoryName(),
    elements: []
  };
  state.nextStrokeId += 1;

  const placed = state.drawMode === "spray"
    ? placeSpray(point.x, point.y, stroke)
    : placeBrush(point.x, point.y, stroke);
  if (!placed) {
    return;
  }

  state.drawing = {
    pointerId: event.pointerId,
    mode: state.drawMode,
    stroke,
    lastPlacedX: point.x,
    lastPlacedY: point.y,
    limitReached: false
  };
  viewport.classList.add("is-drawing");
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
  viewport.classList.remove("is-drawing");
}

function startShapeDrawing(event) {
  if (!ensureDrawableBrushes()) {
    return;
  }

  const point = screenToWorld(event.clientX, event.clientY);
  if (
    state.shapeDraft &&
    state.shapeDraft.mode === state.drawMode &&
    state.shapeDraft.pointerId === null
  ) {
    state.shapeDraft.pointerId = event.pointerId;
    state.shapeDraft.fromPending = true;
    state.shapeDraft.currentX = point.x;
    state.shapeDraft.currentY = point.y;
    state.shapeDraft.startClientX = event.clientX;
    state.shapeDraft.startClientY = event.clientY;
    state.shapeDraft.dragging = false;
  } else {
    cancelShapeDraft();
    state.shapeDraft = {
      mode: state.drawMode,
      anchorX: point.x,
      anchorY: point.y,
      currentX: point.x,
      currentY: point.y,
      pointerId: event.pointerId,
      fromPending: false,
      dragging: false,
      startClientX: event.clientX,
      startClientY: event.clientY
    };
  }

  viewport.classList.add("is-drawing");
  updateShapePreview(
    state.shapeDraft.mode,
    state.shapeDraft.anchorX,
    state.shapeDraft.anchorY,
    point.x,
    point.y
  );
  viewport.setPointerCapture(event.pointerId);
}

function updateShapeDrawing(event) {
  const draft = state.shapeDraft;
  if (!draft) {
    return;
  }

  const point = screenToWorld(event.clientX, event.clientY);
  if (draft.pointerId === event.pointerId) {
    const dragDistance = Math.hypot(event.clientX - draft.startClientX, event.clientY - draft.startClientY);
    if (dragDistance >= SHAPE_DRAG_THRESHOLD_PX) {
      draft.dragging = true;
    }
    draft.currentX = point.x;
    draft.currentY = point.y;
    updateShapePreview(draft.mode, draft.anchorX, draft.anchorY, point.x, point.y);
    return;
  }

  if (draft.pointerId === null) {
    updateShapePreview(draft.mode, draft.anchorX, draft.anchorY, point.x, point.y);
  }
}

async function stopShapeDrawing(pointerId) {
  const draft = state.shapeDraft;
  if (!draft || draft.pointerId !== pointerId) {
    return;
  }

  if (viewport.hasPointerCapture(pointerId)) {
    viewport.releasePointerCapture(pointerId);
  }

  viewport.classList.remove("is-drawing");
  if (!draft.dragging && !draft.fromPending) {
    draft.pointerId = null;
    draft.currentX = draft.anchorX;
    draft.currentY = draft.anchorY;
    hideShapePreview();
    return;
  }

  const { mode, anchorX, anchorY, currentX, currentY } = draft;
  state.shapeDraft = null;
  hideShapePreview();
  try {
    await commitShapeStroke(mode, anchorX, anchorY, currentX, currentY);
  } catch (error) {
    // commitShapeStroke has already restored UI state and reported the failure.
  }
}

function startPanning(event, captureElement = viewport) {
  resetCursorTrailAnchor();
  hideBrushCursorPreview();
  state.panning = {
    pointerId: event.pointerId,
    button: event.button,
    lastClientX: event.clientX,
    lastClientY: event.clientY
  };
  updatePanningStateClass();
  const captureTarget = captureElement || viewport;
  try {
    captureTarget.setPointerCapture(event.pointerId);
  } catch (error) {
    // Pointer capture can fail if pointer already ended; continue without capture.
  }
}

function stopPanning(pointerId) {
  if (!state.panning || state.panning.pointerId !== pointerId) {
    return;
  }

  if (viewport.hasPointerCapture(pointerId)) {
    viewport.releasePointerCapture(pointerId);
  }
  if (exportOverlay.hasPointerCapture(pointerId)) {
    exportOverlay.releasePointerCapture(pointerId);
  }
  state.panning = null;
  updatePanningStateClass();
  updateEraseCursorVisibility();
  scheduleSessionSave();
}

function onPointerDown(event) {
  if (state.exportMode || state.placementTask) {
    return;
  }

  state.pointerInViewport = true;
  state.lastPointerClientX = event.clientX;
  state.lastPointerClientY = event.clientY;
  updateEraseCursorPosition(event.clientX, event.clientY);
  updateEraseCursorVisibility();
  updateBrushCursorPreview();

  if (event.pointerType === "touch") {
    state.touchPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    if (state.touchPointers.size >= 2) {
      event.preventDefault();
      startTouchGestureFromActiveTouches();
      return;
    }
  }

  if (event.button === 1 || event.button === 2) {
    event.preventDefault();
    hideBrushCursorPreview();
    startPanning(event);
    updateEraseCursorVisibility();
    return;
  }

  if (event.button !== 0) {
    return;
  }

  event.preventDefault();
  if (startEditLayerMove(event)) {
    return;
  }

  if (isLeftDragPanModeActive()) {
    hideBrushCursorPreview();
    startPanning(event);
    updateEraseCursorVisibility();
    return;
  }

  if (!isDrawingModeActive()) {
    return;
  }

  if (state.eraseMode) {
    hideBrushCursorPreview();
    startErasing(event);
    return;
  }

  if (isShapeDrawMode(state.drawMode)) {
    hideBrushCursorPreview();
    startShapeDrawing(event);
    return;
  }

  hideBrushCursorPreview();
  startDrawing(event);
}

function onPointerMove(event) {
  if (state.exportMode || state.placementTask) {
    return;
  }

  state.pointerInViewport = true;
  state.lastPointerClientX = event.clientX;
  state.lastPointerClientY = event.clientY;
  updateEraseCursorPosition(event.clientX, event.clientY);
  updateEraseCursorVisibility();
  updateBrushCursorPreview();

  if (state.editLayerMove && state.editLayerMove.pointerId === event.pointerId) {
    updateEditLayerMove(event);
    return;
  }

  if (event.pointerType === "touch") {
    state.touchPointers.set(event.pointerId, { x: event.clientX, y: event.clientY });
    if (state.touchGesture) {
      event.preventDefault();
      updateTouchGestureFromActiveTouches();
      return;
    }
  }

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
    queueErasePoint(state.erasing, point.x, point.y);
  }

  if (state.shapeDraft) {
    if (state.shapeDraft.pointerId === event.pointerId) {
      event.preventDefault();
    }
    updateShapeDrawing(event);
  }

  updateCursorTrailAtClientPoint(event.clientX, event.clientY);
}

function onPointerUp(event) {
  if (state.exportMode) {
    return;
  }

  if (event.pointerType === "touch") {
    state.touchPointers.delete(event.pointerId);
    if (
      state.touchGesture &&
      (state.touchGesture.pointerIdA === event.pointerId || state.touchGesture.pointerIdB === event.pointerId)
    ) {
      endTouchGesture();
    }
  }

  stopPanning(event.pointerId);
  stopEditLayerMove(event.pointerId);
  stopErasing(event.pointerId);
  stopShapeDrawing(event.pointerId);
  stopDrawing(event.pointerId);
  updateEraseCursorVisibility();
  updateBrushCursorPreview();
}

function onWheel(event) {
  if (event.defaultPrevented) {
    return;
  }

  event.preventDefault();
  resetCursorTrailAnchor();

  const normalizedDelta = getNormalizedWheelDelta(event);
  const wheelUnits = -normalizedDelta / 100;
  if (wheelUnits === 0) {
    return;
  }

  if (isRotationWheelShortcutActive(event)) {
    const rotationStepPerUnit = 6;
    const nextRotation =
      parseNumericInputValue(rotationSlider, 0) + wheelUnits * rotationStepPerUnit;
    setInputNumericValue(rotationSlider, nextRotation);
    updateSliderText();
    updateRotationIndicator();
    updateActiveStrokeTailRotation();
    showShortcutPreviewAt(event.clientX, event.clientY);
    updateBrushCursorPreview();
    scheduleSessionSave();
    return;
  }

  const rightButtonHeld =
    (Number(event.buttons) & 2) === 2 ||
    (state.panning && state.panning.button === 2);
  if (rightButtonHeld) {
    const targetSlider = consistentToggle.checked ? consistentSizeSlider : sizeSlider;
    const sizeStepPerUnit = consistentToggle.checked ? 6 : 14;
    const nextSize =
      parseNumericInputValue(targetSlider, Number(targetSlider.value) || 0) +
      wheelUnits * sizeStepPerUnit;
    setInputNumericValue(targetSlider, nextSize);
    updateSliderText();
    updateEraseCursorGeometry();
    showShortcutPreviewAt(event.clientX, event.clientY);
    updateBrushCursorPreview();
    scheduleSessionSave();
    return;
  }

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
  cancelShapeDraft();
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
    cancelShapeDraft();
  }
  if (!state.eraseMode && state.erasing) {
    stopErasing(state.erasing.pointerId);
  }
  if (state.pointerInViewport) {
    updateEraseCursorPosition(state.lastPointerClientX, state.lastPointerClientY);
  }
  updateEraseModeUI();
  updateBrushCursorPreview();
}

function onExportSelectionPointerDown(event) {
  if (!state.exportMode) {
    return;
  }

  if (state.exportTask) {
    event.preventDefault();
    event.stopPropagation();
    return;
  }

  if (event.button === 1 || event.button === 2) {
    event.preventDefault();
    event.stopPropagation();
    startPanning(event, exportOverlay);
    return;
  }

  if (event.button !== 0) {
    return;
  }

  event.preventDefault();
  event.stopPropagation();

  const handle = event.target.closest(".export-edge-handle");
  if (handle) {
    const edge = handle.dataset.edge;
    if (!edge) {
      return;
    }

    startExportSelectionDrag(event.pointerId, {
      mode: "resize",
      edge,
      clientX: event.clientX,
      clientY: event.clientY
    });
    return;
  }

  startExportSelectionDrag(event.pointerId, {
    mode: "move",
    clientX: event.clientX,
    clientY: event.clientY
  });
}

function onExportOverlayPointerDown(event) {
  if (!state.exportMode) {
    return;
  }

  if (state.exportTask) {
    event.preventDefault();
    return;
  }

  if (event.button !== 1 && event.button !== 2) {
    return;
  }

  event.preventDefault();
  startPanning(event, exportOverlay);
}

function onExportOverlayPointerMove(event) {
  if (!state.exportMode) {
    return;
  }

  if (state.exportTask) {
    event.preventDefault();
    return;
  }

  if (state.panning && state.panning.pointerId === event.pointerId) {
    event.preventDefault();
    const dx = event.clientX - state.panning.lastClientX;
    const dy = event.clientY - state.panning.lastClientY;
    state.camera.x += dx;
    state.camera.y += dy;
    state.panning.lastClientX = event.clientX;
    state.panning.lastClientY = event.clientY;
    renderCamera();
    return;
  }

  if (!state.exportDrag) {
    return;
  }

  event.preventDefault();
  updateExportSelectionDrag(event.pointerId, event.clientX, event.clientY, {
    shiftKey: event.shiftKey,
    altKey: event.altKey
  });
}

function onExportOverlayPointerUp(event) {
  if (!state.exportMode) {
    return;
  }
  stopPanning(event.pointerId);
  stopExportSelectionDrag(event.pointerId);
}

function onExportScaleButtonClick(event) {
  const button = event.target.closest(".export-scale-button");
  if (!button || !state.exportMode || state.exportTask) {
    return;
  }
  event.preventDefault();
  setExportScalePercent(Number(button.dataset.scale));
}

function onExportResolutionInput(axis, input) {
  if (!input || state.exportTask || String(input.value).trim() === "") {
    return;
  }
  setExportResolutionFromInput(axis, input.value);
}

initializeSliderGroupToggles();

brushDataToggleButton.addEventListener("click", () => {
  setBrushGalleryCollapsed(!state.brushGalleryCollapsed);
  scheduleSessionSave();
});
dropZonePrompt.addEventListener("click", () => brushInput.click());
dropZonePrompt.addEventListener("keydown", onDropZoneKeyDown);
unloadBrushDataButton.addEventListener("click", (event) => {
  event.preventDefault();
  event.stopPropagation();
  unloadBrushDataSelection();
});
brushGallery.addEventListener("click", onBrushGalleryClick);
brushGallery.addEventListener("contextmenu", onBrushGalleryContextMenu);
brushGallery.addEventListener("dragstart", onBrushGalleryDragStart);
brushGallery.addEventListener("dragend", onBrushGalleryDragEnd);
if (editLayerList) {
  editLayerList.addEventListener("click", (event) => {
    const row = event.target.closest(".edit-layer-row");
    const sequenceRow = event.target.closest(".edit-layer-sequence-row");
    const sequenceSettings = event.target.closest(".edit-layer-sequence-settings");
    const sequenceAddRow = event.target.closest(".edit-layer-sequence-add-row");
    const strokeId = Number(
      row?.dataset.strokeId ||
        sequenceRow?.dataset.strokeId ||
        sequenceSettings?.dataset.strokeId ||
        sequenceAddRow?.dataset.strokeId
    );
    const stroke = state.strokeById.get(strokeId);
    if (!stroke) {
      return;
    }

    const animationButton = event.target.closest(".edit-layer-animation-button");
    if (animationButton) {
      event.preventDefault();
      stroke.animationPaused = !stroke.animationPaused;
      applyStrokeAnimationPaused(stroke);
      selectEditLayer(stroke.id);
      renderEditLayers();
      scheduleSessionSave();
      return;
    }

    const sequenceButton = event.target.closest(".edit-layer-sequence-button");
    if (sequenceButton) {
      event.preventDefault();
      const willOpen = !stroke.sequenceOpen;
      stroke.sequenceOpen = willOpen;
      if (willOpen && typeof stroke.sequenceEnabled !== "boolean") {
        stroke.sequenceEnabled = true;
      }
      selectEditLayer(stroke.id);
      renderEditLayers();
      scheduleSessionSave();
      return;
    }

    const sequenceEnabledButton = event.target.closest(".edit-layer-sequence-enable-button");
    if (sequenceEnabledButton) {
      event.preventDefault();
      stroke.sequenceEnabled = !isLayerSequenceEnabled(stroke);
      refreshStrokeSequenceEffect(stroke);
      selectEditLayer(stroke.id);
      renderEditLayers();
      scheduleSessionSave();
      return;
    }

    const sequenceAddButton = event.target.closest(".edit-layer-sequence-add-button");
    if (sequenceAddButton) {
      event.preventDefault();
      const extras = getExtraLayerSequenceSlots(stroke);
      if (extras.length < MAX_LAYER_SEQUENCE_EFFECTS - 1) {
        extras.push(normalizeLayerSequenceSlot({
          effect: "show-hide",
          timingStyle: "pulse",
          settings: LAYER_SEQUENCE_DEFAULT_SETTINGS
        }));
        setExtraLayerSequenceSlots(stroke, extras);
        stroke.sequenceEnabled = true;
        refreshStrokeSequenceEffect(stroke);
        selectEditLayer(stroke.id);
        renderEditLayers();
        scheduleSessionSave();
      }
      return;
    }

    const sequenceRemoveButton = event.target.closest(".edit-layer-sequence-remove-button");
    if (sequenceRemoveButton) {
      event.preventDefault();
      const slotIndex = Math.floor(Number(sequenceRemoveButton.dataset.sequenceSlotIndex));
      if (slotIndex > 0) {
        const extras = getExtraLayerSequenceSlots(stroke);
        extras.splice(slotIndex - 1, 1);
        setExtraLayerSequenceSlots(stroke, extras);
        refreshStrokeSequenceEffect(stroke);
        selectEditLayer(stroke.id);
        renderEditLayers();
        scheduleSessionSave();
      }
      return;
    }

    const visibilityButton = event.target.closest(".edit-layer-eye-button");
    if (visibilityButton) {
      event.preventDefault();
      stroke.hidden = !stroke.hidden;
      applyStrokeVisibility(stroke);
      selectEditLayer(stroke.id);
      scheduleSessionSave();
      return;
    }

    if (row) {
      selectEditLayer(stroke.id);
    }
  });

  editLayerList.addEventListener("change", (event) => {
    const settingInput = event.target.closest(".edit-layer-sequence-setting-input");
    if (settingInput) {
      const settingsPanelElement = settingInput.closest(".edit-layer-sequence-settings");
      const stroke = state.strokeById.get(Number(settingsPanelElement?.dataset.strokeId));
      if (!stroke) {
        return;
      }
      const key = settingInput.dataset.sequenceSetting || "";
      const value = settingInput.dataset.sequenceSettingType === "boolean"
        ? settingInput.checked
        : getSequenceSettingInputValue(settingInput);
      setLayerSequenceSetting(stroke, key, value, Number(settingInput.dataset.sequenceSlotIndex) || 0);
      refreshStrokeSequenceEffect(stroke);
      selectEditLayer(stroke.id);
      if (settingInput.dataset.sequenceSettingType === "boolean") {
        renderEditLayers();
      }
      scheduleSessionSave();
      return;
    }

    const select = event.target.closest(".edit-layer-sequence-select");
    if (!select) {
      return;
    }
    const sequenceRow = select.closest(".edit-layer-sequence-row");
    const stroke = state.strokeById.get(Number(sequenceRow?.dataset.strokeId));
    if (!stroke) {
      return;
    }
    setLayerSequenceValue(
      stroke,
      select.dataset.sequenceGroup || "effects",
      select.value,
      Number(select.dataset.sequenceSlotIndex) || 0
    );
    stroke.sequenceEnabled = true;
    refreshStrokeSequenceEffect(stroke);
    selectEditLayer(stroke.id);
    renderEditLayers();
    scheduleSessionSave();
  });

  editLayerList.addEventListener("input", (event) => {
    const settingInput = event.target.closest(".edit-layer-sequence-setting-input");
    if (!settingInput) {
      return;
    }
    const settingsPanelElement = settingInput.closest(".edit-layer-sequence-settings");
    const stroke = state.strokeById.get(Number(settingsPanelElement?.dataset.strokeId));
    if (!stroke) {
      return;
    }
    if (settingInput.dataset.sequenceSettingType === "string") {
      setLayerSequenceSetting(
        stroke,
        settingInput.dataset.sequenceSetting || "",
        settingInput.value,
        Number(settingInput.dataset.sequenceSlotIndex) || 0
      );
      refreshStrokeSequenceEffect(stroke);
      scheduleSessionSave();
      return;
    }
    if (settingInput.dataset.sequenceSettingType !== "number") {
      return;
    }
    setLayerSequenceSetting(
      stroke,
      settingInput.dataset.sequenceSetting || "",
      getSequenceSettingInputValue(settingInput),
      Number(settingInput.dataset.sequenceSlotIndex) || 0
    );
    refreshStrokeSequenceEffect(stroke);
    const valueLabel = settingInput.parentElement?.querySelector(".edit-layer-sequence-setting-value");
    if (valueLabel) {
      const suffix = valueLabel.textContent.endsWith("ms")
        ? "ms"
        : valueLabel.textContent.endsWith("%")
        ? "%"
        : "";
      valueLabel.textContent = `${getSequenceSettingInputValue(settingInput)}${suffix}`;
    }
    scheduleSessionSave();
  });

  editLayerList.addEventListener("pointerdown", (event) => {
	    if (
	      event.button !== 0 ||
      event.target.closest(".edit-layer-eye-button") ||
      event.target.closest(".edit-layer-animation-button") ||
      event.target.closest(".edit-layer-sequence-button") ||
      event.target.closest(".edit-layer-sequence-enable-button") ||
      event.target.closest(".edit-layer-sequence-row") ||
	      event.target.closest(".edit-layer-sequence-settings") ||
	      event.target.closest(".edit-layer-sequence-add-row")
	    ) {
	      return;
	    }
    const row = event.target.closest(".edit-layer-row");
    if (row) {
      startEditLayerRowDrag(row, event);
    }
  });
}
if (stockBrushButtons) {
  stockBrushButtons.addEventListener("click", (event) => {
    const button = event.target.closest(".stock-brush-button");
    if (!button || button.disabled) {
      return;
    }
    event.preventDefault();
    void loadStockBrushFolder(button.dataset.stockBrushFolderId || "");
  });
}
if (loadAllStockBrushesButton) {
  loadAllStockBrushesButton.addEventListener("click", (event) => {
    event.preventDefault();
    void loadAllStockBrushFolders();
  });
}
for (const favoriteLoaderButton of [loadFavoriteBrushesButton, loadFavoriteBrushesFullButton]) {
  if (favoriteLoaderButton) {
    favoriteLoaderButton.addEventListener("click", (event) => {
      event.preventDefault();
      void loadFavoriteBrushes();
    });
  }
}
for (const presetContainer of [drawingBrushPresetButtons, brushesBrushPresetButtons]) {
  if (presetContainer) {
    presetContainer.addEventListener("click", onCustomBrushPresetClick);
    presetContainer.addEventListener("dragover", onCustomBrushPresetDragOver);
    presetContainer.addEventListener("drop", onCustomBrushPresetDrop);
  }
}
if (brushSortSelect) {
  brushSortSelect.addEventListener("change", () => {
    state.brushGallerySort = normalizeBrushGallerySort(brushSortSelect.value);
    renderBrushGallery();
    scheduleSessionSave();
  });
}
if (saveCompositionButton) {
  saveCompositionButton.addEventListener("click", () => {
    void saveCurrentComposition();
  });
}
if (savedCompositionsGallery) {
  savedCompositionsGallery.addEventListener("click", (event) => {
    const deleteButton = event.target.closest(".saved-composition-delete-button");
    if (deleteButton) {
      event.preventDefault();
      event.stopPropagation();
      openSavedDeleteConfirmModal(deleteButton.dataset.savedCompositionDeleteId || "");
      return;
    }

    const loadButton = event.target.closest(".saved-composition-load-button");
    if (!loadButton) {
      return;
    }
    event.preventDefault();
    const card = loadButton.closest(".saved-composition-card");
    if (!card) {
      return;
    }
    void loadSavedComposition(card.dataset.savedCompositionId || "");
  });
}
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
  updateBrushCursorPreview();
  scheduleSessionSave();
});
consistentToggle.addEventListener("change", () => {
  updateConsistentModeUI();
  updateEraseCursorGeometry();
  updateBrushCursorPreview();
  scheduleSessionSave();
});
consistentSizeSlider.addEventListener("input", () => {
  updateSliderText();
  updateEraseCursorGeometry();
  updateBrushCursorPreview();
  scheduleSessionSave();
});
spacingSlider.addEventListener("input", () => {
  updateSliderText();
  scheduleSessionSave();
});
rotationSlider.addEventListener("input", () => {
  updateSliderText();
  updateRotationIndicator();
  updateActiveStrokeTailRotation();
  updateBrushCursorPreview();
  scheduleSessionSave();
});
rotationIndicator.addEventListener("pointerdown", onRotationIndicatorPointerDown);
rotationIndicator.addEventListener("pointermove", onRotationIndicatorPointerMove);
rotationIndicator.addEventListener("pointerup", (event) => {
  stopRotationIndicatorDrag(event.pointerId);
});
rotationIndicator.addEventListener("pointercancel", (event) => {
  stopRotationIndicatorDrag(event.pointerId);
});
rotationIndicator.addEventListener("lostpointercapture", (event) => {
  if (state.rotationIndicatorDrag && state.rotationIndicatorDrag.pointerId === event.pointerId) {
    state.rotationIndicatorDrag = null;
    rotationIndicator.classList.remove("is-dragging");
  }
});
rotationIndicator.addEventListener("dblclick", (event) => {
  event.preventDefault();
  setInputNumericValue(rotationSlider, 0);
  updateSliderText();
  updateRotationIndicator();
  updateActiveStrokeTailRotation();
  updateBrushCursorPreview();
  scheduleSessionSave();
});
tintPickerButton.addEventListener("pointerdown", (event) => {
  if (!state.tintPopoverOpen) {
    return;
  }
  event.preventDefault();
  setTintPopoverOpen(false);
  suppressTintPickerClick = true;
});
tintPickerButton.addEventListener("click", (event) => {
  event.preventDefault();
  if (suppressTintPickerClick) {
    suppressTintPickerClick = false;
    return;
  }
  setTintPopoverOpen(!state.tintPopoverOpen);
});
if (tintColorField) {
  tintColorField.addEventListener("pointerdown", (event) => {
    if (!state.tintPopoverOpen) {
      return;
    }
    event.preventDefault();
    event.stopPropagation();

    if (isNativeTintPickerActive()) {
      suppressNextTintInputClick = true;
      closeNativeTintPicker();
      return;
    }

    suppressNextTintInputClick = false;
    openNativeTintPicker();
  });
}
tintColorInput.addEventListener("click", (event) => {
  event.stopPropagation();
  if (!suppressNextTintInputClick) {
    return;
  }
  event.preventDefault();
  suppressNextTintInputClick = false;
});
tintColorInput.addEventListener("focus", () => {
  tintNativePickerOpen = true;
});
tintColorInput.addEventListener("blur", () => {
  tintNativePickerOpen = false;
});
tintColorInput.addEventListener("input", () => {
  applyTintSettingsFromInputs();
  updateBrushCursorPreview();
  scheduleSessionSave();
});
tintAmountSlider.addEventListener("input", () => {
  applyTintSettingsFromInputs();
  updateBrushCursorPreview();
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
brushPreviewToggle.addEventListener("change", () => {
  state.brushPreviewEnabled = brushPreviewToggle.checked;
  updateBrushCursorPreview();
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
if (drawModeButtons) {
  drawModeButtons.addEventListener("click", (event) => {
    const button = event.target.closest(".draw-mode-button");
    if (!button) {
      return;
    }
    event.preventDefault();
    setDrawMode(button.dataset.drawMode || "pencil");
  });
}
spraySpreadSlider.addEventListener("input", () => {
  updateSliderText();
  scheduleSessionSave();
});
if (mainModeBar) {
  mainModeBar.addEventListener("click", (event) => {
    if (state.exportTask) {
      event.preventDefault();
      return;
    }
    const button = event.target.closest(".main-mode-tab-button");
    if (!button || button === exportModeButton) {
      return;
    }
    event.preventDefault();
    if (button.dataset.sidebarTab === "settings" && state.sidebarTab === "settings") {
      setSidebarTab(state.previousSidebarTab || "draw");
      return;
    }
    setSidebarTab(button.dataset.sidebarTab || "draw");
  });
}
if (sidebarOptionsButton) {
  sidebarOptionsButton.addEventListener("click", () => {
    if (state.exportTask) {
      return;
    }
    setSidebarTab(
      state.sidebarTab === "settings"
        ? state.previousSidebarTab || "draw"
        : "settings"
    );
  });
}
sidebarToggleButton.addEventListener("click", () => {
  state.sidebarCollapsed = !state.sidebarCollapsed;
  updateSidebarVisibilityUI();
  scheduleSessionSave();
});
if (drawCanvasBgColorInput) {
  drawCanvasBgColorInput.addEventListener("pointerdown", (event) => {
    event.stopPropagation();
    if (!isCanvasBgPickerActive()) {
      return;
    }
    event.preventDefault();
    suppressNextCanvasBgInputClick = true;
    closeCanvasBgPicker();
  });
  drawCanvasBgColorInput.addEventListener("click", (event) => {
    event.stopPropagation();
    if (!suppressNextCanvasBgInputClick) {
      return;
    }
    event.preventDefault();
    suppressNextCanvasBgInputClick = false;
  });
  drawCanvasBgColorInput.addEventListener("focus", () => {
    canvasBgNativePickerOpen = true;
  });
  drawCanvasBgColorInput.addEventListener("blur", () => {
    canvasBgNativePickerOpen = false;
    suppressNextCanvasBgInputClick = false;
  });
  drawCanvasBgColorInput.addEventListener("input", () => {
    applyCanvasBackgroundColor(drawCanvasBgColorInput.value);
    scheduleSessionSave();
  });
}
if (drawCanvasBgColorLabel) {
  drawCanvasBgColorLabel.addEventListener("pointerdown", (event) => {
    event.stopPropagation();
    if (!isCanvasBgPickerActive()) {
      return;
    }
    event.preventDefault();
    suppressNextCanvasBgInputClick = true;
    closeCanvasBgPicker();
  });
  drawCanvasBgColorLabel.addEventListener("click", (event) => {
    event.stopPropagation();
    if (!suppressNextCanvasBgInputClick) {
      return;
    }
    event.preventDefault();
    suppressNextCanvasBgInputClick = false;
  });
}
canvasBgColorInput.addEventListener("pointerdown", (event) => {
  event.stopPropagation();
  if (!isCanvasBgPickerActive()) {
    return;
  }
  event.preventDefault();
  suppressNextCanvasBgInputClick = true;
  closeCanvasBgPicker();
});
canvasBgColorInput.addEventListener("click", (event) => {
  event.stopPropagation();
  if (!suppressNextCanvasBgInputClick) {
    return;
  }
  event.preventDefault();
  suppressNextCanvasBgInputClick = false;
});
if (canvasBgColorLabel) {
  canvasBgColorLabel.addEventListener("pointerdown", (event) => {
    event.stopPropagation();
    if (!isCanvasBgPickerActive()) {
      return;
    }
    event.preventDefault();
    suppressNextCanvasBgInputClick = true;
    closeCanvasBgPicker();
  });
  canvasBgColorLabel.addEventListener("click", (event) => {
    event.stopPropagation();
    if (!suppressNextCanvasBgInputClick) {
      return;
    }
    event.preventDefault();
    suppressNextCanvasBgInputClick = false;
  });
}
canvasBgColorInput.addEventListener("focus", () => {
  canvasBgNativePickerOpen = true;
});
canvasBgColorInput.addEventListener("blur", () => {
  canvasBgNativePickerOpen = false;
  suppressNextCanvasBgInputClick = false;
});
canvasBgColorInput.addEventListener("input", () => {
  applyCanvasBackgroundColor(canvasBgColorInput.value);
  scheduleSessionSave();
});
if (exportCanvasBgColorLabel) {
  exportCanvasBgColorLabel.addEventListener("pointerdown", (event) => {
    event.stopPropagation();
  });
}
if (exportCanvasBgColorInput) {
  exportCanvasBgColorInput.addEventListener("input", () => {
    applyCanvasBackgroundColor(exportCanvasBgColorInput.value);
    scheduleSessionSave();
  });
}
if (exportBgImageButton && exportBgImageInput) {
  exportBgImageButton.addEventListener("click", () => {
    exportBgImageInput.click();
  });
}
if (clearExportBgImageButton) {
  clearExportBgImageButton.addEventListener("click", (event) => {
    event.stopPropagation();
    clearExportBackgroundImage();
  });
}
if (exportBgImageInput) {
  exportBgImageInput.addEventListener("change", () => {
    const file = exportBgImageInput.files && exportBgImageInput.files[0]
      ? exportBgImageInput.files[0]
      : null;
    loadExportBackgroundImageFile(file);
    exportBgImageInput.value = "";
  });
}
if (exportBgImageOpacitySlider) {
  exportBgImageOpacitySlider.addEventListener("input", () => {
    state.exportBgImageOpacity = clamp(Number(exportBgImageOpacitySlider.value) || 0, 0, 100);
    exportBackgroundRenderCache.clear();
    updateExportBackgroundImageUI();
    scheduleSessionSave();
  });
}
if (exportBgImageTileToggle) {
  exportBgImageTileToggle.addEventListener("change", () => {
    state.exportBgImageMode = exportBgImageTileToggle.checked ? "tile" : "stretch";
    exportBackgroundRenderCache.clear();
    updateExportBackgroundImageUI();
    scheduleSessionSave();
  });
}
if (exportBgImageTileSizeSlider) {
  exportBgImageTileSizeSlider.addEventListener("input", () => {
    state.exportBgImageTileSize = mapExportBgTileSliderToSize(exportBgImageTileSizeSlider.value);
    exportBackgroundRenderCache.clear();
    updateExportBackgroundImageUI();
    scheduleSessionSave();
  });
}
exportBackgroundToggle.addEventListener("change", () => {
  state.exportBackgroundEnabled = exportBackgroundToggle.checked;
  updateSettingsPanelUI();
  updateExportBackgroundImageUI();
  updateExportOverlayGeometry();
  scheduleSessionSave();
});
if (exportSeeBeyondToggle) {
  exportSeeBeyondToggle.addEventListener("change", () => {
    state.exportSeeBeyondEnabled = exportSeeBeyondToggle.checked;
    updateExportOverlayGeometry();
    scheduleSessionSave();
  });
}
gifCountToggle.addEventListener("change", () => {
  state.showGifCountIndicator = gifCountToggle.checked;
  updateGifCountIndicator();
  scheduleSessionSave();
});
gifPauseToggle.addEventListener("change", () => {
  state.showGifPauseButton = gifPauseToggle.checked;
  updateGifPauseButtonUI();
  scheduleSessionSave();
});
if (drawBkgColorToggle) {
  drawBkgColorToggle.addEventListener("change", () => {
    state.showDrawBackgroundColorControl = drawBkgColorToggle.checked;
    updateSettingsPanelUI();
    scheduleSessionSave();
  });
}
eraseModeButton.addEventListener("click", () => {
  setEraseMode(!state.eraseMode);
});
undoButton.addEventListener("click", undoLastStroke);
redoButton.addEventListener("click", redoLastStroke);
clearButton.addEventListener("click", openClearConfirmModal);
exportModeButton.addEventListener("click", () => {
  if (state.sidebarTab === "export" && state.sidebarCollapsed) {
    state.sidebarCollapsed = false;
    updateSidebarVisibilityUI();
    scheduleSessionSave();
    return;
  }
  setSidebarTab("export", { keepExportMode: true });
  enterExportMode();
});
exportButton.addEventListener("click", () => {
  void confirmExport();
});
exportCancelButton.addEventListener("click", () => {
  if (!state.exportTask) {
    return;
  }
  cancelExportTask();
});
if (exportVideoButton) {
  exportVideoButton.addEventListener("click", () => {
    void confirmVideoExport();
  });
}
if (exportVideoCancelButton) {
  exportVideoCancelButton.addEventListener("click", () => {
    if (!state.exportTask) {
      return;
    }
    cancelExportTask();
  });
}
gifPauseButton.addEventListener("click", () => {
  setGifAnimationsPaused(!state.gifAnimationsPaused);
});
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
if (savedDeleteConfirmYesButton) {
  savedDeleteConfirmYesButton.addEventListener("click", () => {
    void confirmDeleteSavedComposition();
  });
}
if (savedDeleteConfirmNoButton) {
  savedDeleteConfirmNoButton.addEventListener("click", closeSavedDeleteConfirmModal);
}
if (savedDeleteConfirmModal) {
  savedDeleteConfirmModal.addEventListener("click", (event) => {
    if (event.target === savedDeleteConfirmModal) {
      closeSavedDeleteConfirmModal();
    }
  });
}
brushCropConfirmButton.addEventListener("click", () => {
  void confirmBrushCropModal();
});
brushCropCancelButton.addEventListener("click", () => {
  closeBrushCropModal();
});
brushCropModal.addEventListener("click", (event) => {
  if (event.target === brushCropModal) {
    closeBrushCropModal();
  }
});
brushCropImage.addEventListener("load", () => {
  renderBrushCropModal();
});
if (brushCropWidthInput) {
  brushCropWidthInput.addEventListener("input", () => {
    state.brushCropEditor.outputWidth = clamp(
      Math.round(Number(brushCropWidthInput.value) || 1),
      1,
      EXPORT_MAX_DIMENSION
    );
    syncBrushCropOutputToAspect("width");
    updateBrushCropResolutionInputs();
  });
}
if (brushCropHeightInput) {
  brushCropHeightInput.addEventListener("input", () => {
    state.brushCropEditor.outputHeight = clamp(
      Math.round(Number(brushCropHeightInput.value) || 1),
      1,
      EXPORT_MAX_DIMENSION
    );
    syncBrushCropOutputToAspect("height");
    updateBrushCropResolutionInputs();
  });
}
if (brushCropResolutionResetButton) {
  brushCropResolutionResetButton.addEventListener("click", () => {
    const nativeSize = getBrushCropNativeOutputSize();
    setBrushCropOutputSize(nativeSize.width, nativeSize.height);
    updateBrushCropResolutionInputs();
  });
}
if (brushCropProbabilityControls) {
  brushCropProbabilityControls.addEventListener("click", (event) => {
    const button = event.target.closest(".brush-crop-probability-button");
    if (!button) {
      return;
    }
    state.brushCropEditor.weightMode = normalizeBrushWeightMode(button.dataset.weightMode);
    updateBrushCropProbabilityUI();
  });
}
if (brushCropFrameTrack) {
  brushCropFrameTrack.addEventListener("pointerdown", (event) => {
    if (!state.brushCropEditor.open || event.button !== 0) {
      return;
    }
    const handle = event.target.closest(".brush-crop-frame-handle");
    const edge = handle?.dataset.frameEdge || "";
    if (edge !== "start" && edge !== "end") {
      return;
    }
    event.preventDefault();
    state.brushCropEditor.frameDrag = {
      pointerId: event.pointerId,
      edge
    };
    handle.setPointerCapture(event.pointerId);
    updateBrushCropFrameRangeFromPointer(event.clientX, edge);
  });
  brushCropFrameTrack.addEventListener("pointermove", (event) => {
    const drag = state.brushCropEditor.frameDrag;
    if (!state.brushCropEditor.open || !drag || drag.pointerId !== event.pointerId) {
      return;
    }
    event.preventDefault();
    updateBrushCropFrameRangeFromPointer(event.clientX, drag.edge);
  });
  const endBrushCropFrameDrag = (event) => {
    const drag = state.brushCropEditor.frameDrag;
    if (!drag || drag.pointerId !== event.pointerId) {
      return;
    }
    const handle = drag.edge === "start" ? brushCropFrameStartHandle : brushCropFrameEndHandle;
    if (handle && handle.hasPointerCapture(event.pointerId)) {
      handle.releasePointerCapture(event.pointerId);
    }
    state.brushCropEditor.frameDrag = null;
  };
  brushCropFrameTrack.addEventListener("pointerup", endBrushCropFrameDrag);
  brushCropFrameTrack.addEventListener("pointercancel", endBrushCropFrameDrag);
}
brushCropSelection.addEventListener("pointerdown", onBrushCropSelectionPointerDown);
brushCropSelection.addEventListener("pointermove", onBrushCropPointerMove);
brushCropSelection.addEventListener("pointerup", onBrushCropPointerUp);
brushCropSelection.addEventListener("pointercancel", onBrushCropPointerUp);
brushCropModal.addEventListener("pointermove", onBrushCropPointerMove);
brushCropModal.addEventListener("pointerup", onBrushCropPointerUp);
brushCropModal.addEventListener("pointercancel", onBrushCropPointerUp);
exportSelection.addEventListener("pointerdown", onExportSelectionPointerDown);
exportSelection.addEventListener("pointermove", onExportOverlayPointerMove);
exportSelection.addEventListener("pointerup", onExportOverlayPointerUp);
exportSelection.addEventListener("pointercancel", onExportOverlayPointerUp);
exportOverlay.addEventListener("pointerdown", onExportOverlayPointerDown);
exportOverlay.addEventListener("pointermove", onExportOverlayPointerMove);
exportOverlay.addEventListener("pointerup", onExportOverlayPointerUp);
exportOverlay.addEventListener("pointercancel", onExportOverlayPointerUp);
exportOverlay.addEventListener("wheel", (event) => {
  if (!state.exportMode) {
    return;
  }
  onWheel(event);
}, { passive: false });
exportOverlay.addEventListener("contextmenu", (event) => {
  if (state.exportMode) {
    event.preventDefault();
  }
});
if (exportScaleButtonsGroup) {
  exportScaleButtonsGroup.addEventListener("click", onExportScaleButtonClick);
}
if (exportSidebarScaleButtonsGroup) {
  exportSidebarScaleButtonsGroup.addEventListener("click", onExportScaleButtonClick);
}
if (exportAnimationAutoToggle) {
  exportAnimationAutoToggle.addEventListener("change", () => {
    state.exportAnimationAuto = exportAnimationAutoToggle.checked;
    updateExportAnimationUI();
    scheduleSessionSave();
  });
}
if (exportAnimationSecondsButtonsGroup) {
  exportAnimationSecondsButtonsGroup.addEventListener("click", (event) => {
    const button = event.target.closest(".export-animation-seconds-button");
    if (!button || button.disabled) {
      return;
    }
    const seconds = Number(button.dataset.seconds);
    if (!EXPORT_MANUAL_SECONDS_PRESETS.includes(seconds)) {
      return;
    }
    state.exportAnimationFrameCount = "";
    state.exportAnimationSeconds = seconds;
    updateExportAnimationUI();
    scheduleSessionSave();
  });
}
if (exportFrameCountInput) {
  exportFrameCountInput.addEventListener("input", () => {
    const value = String(exportFrameCountInput.value || "").trim();
    if (!value) {
      state.exportAnimationFrameCount = "";
    } else {
      state.exportAnimationFrameCount = String(
        clamp(Math.floor(Number(value)) || 1, 1, EXPORT_MAX_FRAME_COUNT)
      );
      if (exportFrameCountInput.value !== state.exportAnimationFrameCount) {
        exportFrameCountInput.value = state.exportAnimationFrameCount;
      }
    }
    updateExportAnimationUI();
    scheduleSessionSave();
  });
}
if (exportVideoAutoToggle) {
  exportVideoAutoToggle.addEventListener("change", () => {
    state.exportVideoAuto = exportVideoAutoToggle.checked;
    updateExportAnimationUI();
    scheduleSessionSave();
  });
}
if (exportVideoLengthInput) {
  exportVideoLengthInput.addEventListener("input", () => {
    const value = String(exportVideoLengthInput.value || "").trim();
    state.exportVideoSeconds = value
      ? clamp(Number(value) || 0, 0, EXPORT_VIDEO_MAX_SECONDS)
      : 0;
    if (value && Number(exportVideoLengthInput.value) !== state.exportVideoSeconds) {
      exportVideoLengthInput.value = String(state.exportVideoSeconds);
    }
    updateExportAnimationUI();
    scheduleSessionSave();
  });
}
exportWidthInput.addEventListener("input", () => {
  onExportResolutionInput("width", exportWidthInput);
});
exportHeightInput.addEventListener("input", () => {
  onExportResolutionInput("height", exportHeightInput);
});
if (exportSidebarWidthInput) {
  exportSidebarWidthInput.addEventListener("input", () => {
    onExportResolutionInput("width", exportSidebarWidthInput);
  });
}
if (exportSidebarHeightInput) {
  exportSidebarHeightInput.addEventListener("input", () => {
    onExportResolutionInput("height", exportSidebarHeightInput);
  });
}
exportWidthInput.addEventListener("blur", () => {
  updateExportOverlayGeometry();
});
exportHeightInput.addEventListener("blur", () => {
  updateExportOverlayGeometry();
});
if (exportSidebarWidthInput) {
  exportSidebarWidthInput.addEventListener("blur", () => {
    updateExportOverlayGeometry();
  });
}
if (exportSidebarHeightInput) {
  exportSidebarHeightInput.addEventListener("blur", () => {
    updateExportOverlayGeometry();
  });
}
exportWidthInput.addEventListener("focus", () => {
  exportWidthInput.select();
});
exportHeightInput.addEventListener("focus", () => {
  exportHeightInput.select();
});
if (exportSidebarWidthInput) {
  exportSidebarWidthInput.addEventListener("focus", () => {
    exportSidebarWidthInput.select();
  });
}
if (exportSidebarHeightInput) {
  exportSidebarHeightInput.addEventListener("focus", () => {
    exportSidebarHeightInput.select();
  });
}
document.addEventListener("pointerdown", (event) => {
  if (!state.tintPopoverOpen) {
    return;
  }
  if (!tintGroup) {
    setTintPopoverOpen(false);
    return;
  }
  const target = event.target;
  if (target instanceof Node && tintGroup.contains(target)) {
    return;
  }
  setTintPopoverOpen(false);
});
document.addEventListener("keydown", (event) => {
  state.ctrlOrMetaHeld = Boolean(event.ctrlKey || event.metaKey);
  if (event.key === "Escape" && state.exportTask) {
    event.preventDefault();
    cancelExportTask();
    return;
  }
  if (event.key === "Escape" && state.placementTask) {
    event.preventDefault();
    cancelPlacementTask();
    return;
  }
  if (event.key === "Escape" && state.brushCropEditor.open) {
    event.preventDefault();
    closeBrushCropModal();
    return;
  }
  if (event.key === "Escape" && state.shapeDraft) {
    event.preventDefault();
    cancelShapeDraft();
    return;
  }
  if (event.key === "Escape" && state.exportMode) {
    event.preventDefault();
    exitExportMode({ focusButton: true });
    return;
  }
  if (event.key === "Escape" && state.tintPopoverOpen) {
    event.preventDefault();
    setTintPopoverOpen(false);
    return;
  }

  const key = String(event.key || "").toLowerCase();
  const hasUndoModifier = event.ctrlKey || event.metaKey;
  if (hasUndoModifier && !event.altKey && key === "z") {
    if (state.exportMode || state.placementTask || state.exportTask) {
      event.preventDefault();
      return;
    }
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
    return;
  }

  if (
    event.key === "Escape" &&
    savedDeleteConfirmModal &&
    savedDeleteConfirmModal.classList.contains("is-open")
  ) {
    closeSavedDeleteConfirmModal();
  }
});
document.addEventListener("keyup", (event) => {
  state.ctrlOrMetaHeld = Boolean(event.ctrlKey || event.metaKey);
});
window.addEventListener("pointermove", updateEditLayerRowDrag);
window.addEventListener("pointerup", (event) => {
  stopEditLayerRowDrag(event.pointerId, event);
});
window.addEventListener("pointercancel", (event) => {
  stopEditLayerRowDrag(event.pointerId);
  stopEditLayerMove(event.pointerId);
});
window.addEventListener("blur", () => {
  stopRotationIndicatorDrag();
  cancelShapeDraft();
  state.editLayerDrag = null;
  setEditLayerDeleteDropzoneState(false, false);
  if (state.editLayerMove) {
    stopEditLayerMove(state.editLayerMove.pointerId);
  }
  if (state.eraseCursorRafId !== null) {
    window.cancelAnimationFrame(state.eraseCursorRafId);
    state.eraseCursorRafId = null;
  }
  state.ctrlOrMetaHeld = false;
  setTintPopoverOpen(false);
  closeCanvasBgPicker();
  suppressNextCanvasBgInputClick = false;
  hideShortcutPreview(true);
  hideBrushCursorPreview();
});

viewport.addEventListener("pointerdown", onPointerDown);
viewport.addEventListener("pointermove", onPointerMove);
viewport.addEventListener("pointerrawupdate", (event) => {
  if (state.exportMode || !state.eraseMode) {
    return;
  }
  updateEraseCursorPosition(event.clientX, event.clientY);
});
viewport.addEventListener("pointerup", onPointerUp);
viewport.addEventListener("pointercancel", onPointerUp);
viewport.addEventListener("pointerenter", (event) => {
  state.pointerInViewport = true;
  state.lastPointerClientX = event.clientX;
  state.lastPointerClientY = event.clientY;
  updateEraseCursorPosition(event.clientX, event.clientY);
  updateEraseCursorVisibility();
  updateBrushCursorPreview();
});
viewport.addEventListener("pointerleave", () => {
  state.pointerInViewport = false;
  resetCursorTrailAnchor();
  updateEraseCursorVisibility();
  hideBrushCursorPreview();
});
viewport.addEventListener("wheel", onWheel, { passive: false });
window.addEventListener("wheel", (event) => {
  if (!state.drawing) {
    return;
  }
  onWheel(event);
}, { passive: false, capture: true });
viewport.addEventListener("contextmenu", (event) => event.preventDefault());
viewport.addEventListener("auxclick", (event) => {
  if (event.button === 1) {
    event.preventDefault();
  }
});
window.addEventListener("pagehide", flushSessionSaveNow);
window.addEventListener("beforeunload", flushSessionSaveNow);
window.addEventListener("resize", () => {
  updateEditLayerDeleteDropzonePosition();
  updateGifPauseButtonPosition();
  if (state.exportMode) {
    updateExportOverlayGeometry();
  }
  if (state.brushCropEditor.open) {
    renderBrushCropModal();
  }
});
controlsPanel.addEventListener("scroll", () => {
  if (state.editLayerDrag) {
    updateEditLayerDeleteDropzonePosition();
  }
});
document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "hidden") {
    flushSessionSaveNow();
  }
});
gifPauseObserver.observe(document.body, { childList: true, subtree: true });

async function initializeApp() {
  loadFavoriteBrushSources();
  loadCustomBrushPresetSources();
  startLayerSequenceLoop();
  const restored = await restoreSessionState();
  if (restored) {
    updateFavoriteBrushButtons();
    return;
  }
  applyCollapsedSliderGroupSnapshot(null);
  updateSliderText();
  updateTintControlUI();
  updateBrushTintMatrix();
  setTintPopoverOpen(false);
  updateConsistentModeUI();
  updateRenderModeUI();
  updateCursorTrailUI();
  updateDrawModeUI();
  updateGifPauseButtonUI();
  updateRotationIndicator();
  updateSidebarVisibilityUI();
  updateSidebarTabUI();
  updateSettingsPanelUI();
  applyCanvasBackgroundColor(state.canvasBackgroundColor);
  updateEraseModeUI();
  updateUndoState();
  updateBrushStatus();
  renderBrushGallery();
  renderStockBrushButtons();
  renderCamera();
}

void initializeApp();
