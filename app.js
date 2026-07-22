const MAX_VISIBLE_STAMPS = 25000;
const BRUSH_GALLERY_PAGE_SIZE = 60;
const DEFAULT_BRUSH_GALLERY_SORT = "alpha";
const BRUSH_SOURCE_LOAD_CONCURRENCY = 4;
const STOCK_BRUSH_ASSET_REVISION = "20260721-optimization-closeout-v1";
const STOCK_BRUSH_ASSET_REVISIONS_BY_FOLDER = new Map([
  ["nu", STOCK_BRUSH_ASSET_REVISION]
]);
const ALLOWED_EXTENSIONS = /\.(png|jpe?g|webp|gif)$/i;
const STOCK_BRUSH_FOLDERS = Array.isArray(window.STOCK_BRUSH_FOLDERS)
  ? window.STOCK_BRUSH_FOLDERS
  : [];
const STOCK_BRUSH_METADATA =
  window.STOCK_BRUSH_METADATA && typeof window.STOCK_BRUSH_METADATA === "object"
    ? window.STOCK_BRUSH_METADATA
    : {};
const STOCK_BRUSH_METADATA_TAGS = new Set([
  "plant",
  "flower",
  "animal",
  "character",
  "anime",
  "pixel-art",
  "glitch",
  "3d",
  "video-game",
  "cartoon",
  "illustration",
  "live-action",
  "abstract",
  "text",
  "framing",
  "particle",
  "lighting",
  "box",
  "cute",
  "spiritual",
  "western",
  "meme",
  "misc"
]);
const STOCK_BRUSH_FOLDER_ORDER = [
  "radial",
  "flower",
  "garden",
  "stroke",
  "squares",
  "esp ra de glitch",
  "esp ra de",
  "esp ra de characters",
  "particles",
  "3d",
  "pixel art+games",
  "anime",
  "misc",
  "framing",
  "nu"
];
const STOCK_BRUSH_FOLDER_ID_ALIASES = new Map([
  ["futari glitch", "squares"],
  ["laser data", "esp ra de glitch"]
]);
const STOCK_BRUSH_SOURCE_ALIASES = new Map([
  ["brushes/3d/ezgif-72b51a95c83cc2f0.png", "brushes/3d/ezgif-72b51a95c83cc2f0.gif"],
  ["brushes/anime/chika.webp", "brushes/anime/chika.gif"],
  [
    "brushes/garden/tumblr_2dfe4903c0e05e36e2db5535c1c13a47_e076b168_100.webp",
    "brushes/garden/tumblr_2dfe4903c0e05e36e2db5535c1c13a47_e076b168_100.gif"
  ],
  ["brushes/misc/cat smash.png", "brushes/misc/cat smash.gif"],
  [
    "brushes/nu/tumblr_6052a87722156ecb140360ddacbc4b6c_909c5a24_640.webp",
    "brushes/nu/tumblr_6052a87722156ecb140360ddacbc4b6c_909c5a24_640.gif"
  ],
  ["brushes/particles/blizzard.png", "brushes/particles/blizzard.gif"],
  ["brushes/particles/snow.png", "brushes/particles/snow.gif"],
  [
    "brushes/pixel art+games/genesta kings quest.png",
    "brushes/pixel art+games/genesta kings quest.gif"
  ]
]);
const DRAW_MODES = ["pencil", "spray", "line", "box", "box-outline", "circle", "circle-outline"];
const SHAPE_DRAW_MODES = new Set(["line", "box", "box-outline", "circle", "circle-outline"]);
const OUTLINE_SHAPE_DRAW_MODES = new Set(["box-outline", "circle-outline"]);
const OUTLINE_DRAW_MODE_BY_BASE = new Map([
  ["box", "box-outline"],
  ["circle", "circle-outline"]
]);
const BASE_DRAW_MODE_BY_OUTLINE = new Map([
  ["box-outline", "box"],
  ["circle-outline", "circle"]
]);
const SIDEBAR_TABS = ["draw", "brushes", "edit", "export", "community", "settings"];
const EDIT_LAYER_LIVE_MOVE_LIMIT = 1000;
const LAYER_MOVE_HISTORY_LIMIT = 50;
const EXPORT_CROP_HISTORY_LIMIT = 100;
const MAX_LAYER_SEQUENCE_EFFECTS = 3;
const LAYER_SEQUENCE_PREVIEW_MAX_BUCKETS = 40;
const LAYER_SEQUENCE_PREVIEW_MIN_DECAY_MS = 160;
const LAYER_SEQUENCE_PREVIEW_MAX_DECAY_MS = 900;
const LAYER_SEQUENCE_PREVIEW_FRAME_INTERVAL_MS = 1000 / 30;
const LAYER_SEQUENCE_SETTING_RESET_DEBOUNCE_MS = 72;
const LAYER_SEQUENCE_MAX_PULSE_CATCH_UP_PER_STAMP = 4;
const LAYER_SEQUENCE_MAX_PULSE_CATCH_UP_PER_FRAME = 256;
const LAYER_SEQUENCE_MAX_WAVE_CATCH_UP_PER_FRAME = 24;
const LAYER_SEQUENCE_EFFECT_OPTIONS = [
  { value: "show-hide", label: "Show/Hide" },
  { value: "move", label: "Move" },
  { value: "rotate", label: "Rotate" },
  { value: "scale", label: "Scale" },
  { value: "color-cycle", label: "Color Cycle" },
  { value: "image-cycle", label: "Image Cycle" },
  { value: "pixelate", label: "Pixelate" },
  { value: "blur", label: "Blur" }
];
const LAYER_SEQUENCE_TIMING_OPTIONS = [
  { value: "pulse", label: "Pulse" },
  { value: "wave", label: "Bounce" },
  { value: "step", label: "Step" },
  { value: "random", label: "Random" },
  { value: "all", label: "All" },
  { value: "grouped", label: "Grouped" }
];
const LAYER_SEQUENCE_GROUPED_EXCLUDED_EFFECTS = new Set([
  "show-hide",
  "color-cycle",
  "image-cycle"
]);
const LAYER_SEQUENCE_MOVE_MODE_OPTIONS = [
  { value: "left", label: "left" },
  { value: "right", label: "right" },
  { value: "up", label: "up" },
  { value: "down", label: "down" },
  { value: "circle", label: "circle" },
  { value: "swing", label: "swing" },
  { value: "random", label: "random" }
];
const LAYER_BLEND_MODE_OPTIONS = [
  { value: "normal", label: "Normal" },
  { value: "multiply", label: "Multiply" },
  { value: "screen", label: "Screen" },
  { value: "overlay", label: "Overlay" },
  { value: "darken", label: "Darken" },
  { value: "lighten", label: "Lighten" },
  { value: "color-dodge", label: "Color Dodge" },
  { value: "color-burn", label: "Color Burn" },
  { value: "hard-light", label: "Hard Light" },
  { value: "soft-light", label: "Soft Light" },
  { value: "difference", label: "Difference" },
  { value: "exclusion", label: "Exclusion" },
  { value: "hue", label: "Hue" },
  { value: "saturation", label: "Saturation" },
  { value: "color", label: "Color" },
  { value: "luminosity", label: "Luminosity" }
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
  pixelateAmount: 16,
  pixelateSpeed: 45,
  blurAmount: 8,
  blurSpeed: 45,
  pulseSpeed: 35,
  pulseRate: 35,
  waveSpeed: 45,
  waveReverse: false,
  stepLength: 350,
  stepAmount: 1,
  stepRate: 350,
  randomSpeed: 45
};
const SESSION_STORAGE_KEY = "random-brush-drawer-session-v1";
const SESSION_STORAGE_POINTER_KEY = `${SESSION_STORAGE_KEY}-pointer`;
const SESSION_STORAGE_PENDING_POINTER_KEY = `${SESSION_STORAGE_KEY}-pending-pointer`;
const SESSION_STORAGE_TAB_ID_KEY = `${SESSION_STORAGE_KEY}-tab-id`;
const SESSION_IDB_PREFIX = "idb:";
const SESSION_IDB_NAME = "image-brush-session-cache";
const SESSION_IDB_STORE_NAME = "snapshots";
const SAVED_COMPOSITIONS_INDEX_KEY = "saved-compositions:index";
const SAVED_COMPOSITION_KEY_PREFIX = "saved-composition:";
const FAVORITE_BRUSH_SOURCES_KEY = "favorite-brush-sources:v1";
const CUSTOM_BRUSH_PRESET_SOURCES_KEY = "custom-brush-preset-sources:v1";
const SAVE_DEBOUNCE_MS = 220;
const SAVE_IDLE_TIMEOUT_MS = 1200;
const SAVE_URGENT_MIN_INTERVAL_MS = 750;
const SAVE_DIRECT_IDB_STAMP_THRESHOLD = 500;
const SESSION_PENDING_SNAPSHOT_RETRY_DELAYS_MS = [25, 75, 150, 300, 500];
const SCENE_RENDER_PROTOCOL = "scene-render";
const SCENE_RENDER_VERSION = 1;
const SCENE_RENDER_MIN_TOTAL_STAMPS = 1600;
const SCENE_RENDER_MIN_ANIMATED_STAMPS = 650;
const SCENE_RENDER_PREPARE_TIMEOUT_MS = 20000;

const viewport = document.getElementById("viewport");
const world = document.getElementById("world");
let sceneRenderCanvas = document.getElementById("sceneRenderCanvas");
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
const brushGalleryPagination = document.getElementById("brushGalleryPagination");
const brushGalleryPreviousPageButton = document.getElementById("brushGalleryPreviousPageButton");
const brushGalleryNextPageButton = document.getElementById("brushGalleryNextPageButton");
const brushGalleryPageStatus = document.getElementById("brushGalleryPageStatus");
const stockBrushButtons = document.getElementById("stockBrushButtons");
const brushSearchControls = document.getElementById("brushSearchControls");
const brushGallerySearchInput = document.getElementById("brushGallerySearchInput");
const brushTagMenuButton = document.getElementById("brushTagMenuButton");
const brushTagMenu = document.getElementById("brushTagMenu");
const brushSortControls = document.getElementById("brushSortControls");
const brushSortSelect = document.getElementById("brushSortSelect");
const stockBrushBrowseRow = document.getElementById("stockBrushBrowseRow");
const browseAllStockBrushesButton = document.getElementById("browseAllStockBrushesButton");
const loadAllStockBrushesButton = document.getElementById("loadAllStockBrushesButton");
const loadFavoriteBrushesButton = document.getElementById("loadFavoriteBrushesButton");
const loadFavoriteBrushesFullButton = document.getElementById("loadFavoriteBrushesFullButton");
const brushImagePickerButton = document.getElementById("brushImagePickerButton");
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
const randomSizeToggle = document.getElementById("randomSizeToggle");
const randomSizeGroup = document.getElementById("randomSizeGroup");
const randomSizeMinSlider = document.getElementById("randomSizeMinSlider");
const randomSizeMaxSlider = document.getElementById("randomSizeMaxSlider");
const randomSizeRangeFill = document.getElementById("randomSizeRangeFill");
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
const exportGuidelinesToggle = document.getElementById("exportGuidelinesToggle");
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
const brushCropStageWrap = document.getElementById("brushCropStageWrap");
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
const brushCropZoomInput = document.getElementById("brushCropZoomInput");
const brushCropZoomOutButton = document.getElementById("brushCropZoomOutButton");
const brushCropZoomInButton = document.getElementById("brushCropZoomInButton");
const brushCropZoomReadout = document.getElementById("brushCropZoomReadout");
const brushCropFrameControls = document.getElementById("brushCropFrameControls");
const brushCropFrameTrack = document.getElementById("brushCropFrameTrack");
const brushCropFrameSegments = document.getElementById("brushCropFrameSegments");
const brushCropFrameSelection = document.getElementById("brushCropFrameSelection");
const brushCropFrameStartHandle = document.getElementById("brushCropFrameStartHandle");
const brushCropFrameEndHandle = document.getElementById("brushCropFrameEndHandle");
const brushCropFrameReadout = document.getElementById("brushCropFrameReadout");
const brushCropProbabilityControls = document.getElementById("brushCropProbabilityControls");
const brushCropTags = document.getElementById("brushCropTags");
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
const exportResolutionLockButton = document.getElementById("exportResolutionLockButton");
const exportSidebarWidthInput = document.getElementById("exportSidebarWidthInput");
const exportSidebarHeightInput = document.getElementById("exportSidebarHeightInput");
const exportSidebarResolutionLockButton = document.getElementById("exportSidebarResolutionLockButton");
const exportScaleButtonsGroup = document.getElementById("exportScaleButtons");
const exportSidebarScaleButtonsGroup = document.getElementById("exportSidebarScaleButtons");
const exportSequencePrewarmInput = document.getElementById("exportSequencePrewarmInput");
const exportAnimationDurationLabel = document.getElementById("exportAnimationDurationLabel");
const exportAnimationAutoToggle = document.getElementById("exportAnimationAutoToggle");
const exportAnimationManualControls = document.getElementById("exportAnimationManualControls");
const exportAnimationSecondsButtonsGroup = document.getElementById("exportAnimationSecondsButtons");
const exportAnimationSecondsButtons = exportAnimationSecondsButtonsGroup
  ? Array.from(exportAnimationSecondsButtonsGroup.querySelectorAll(".export-animation-seconds-button"))
  : [];
const exportFrameCountInput = document.getElementById("exportFrameCountInput");
const exportGifSizeLimitToggle = document.getElementById("exportGifSizeLimitToggle");
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
const EXPORT_GIF_MAX_SIZE_BYTES = 15 * 1000 * 1000;
const EXPORT_GIF_SIZE_TARGET_BYTES = Math.floor(EXPORT_GIF_MAX_SIZE_BYTES * 0.985);
const EXPORT_GIF_SIZE_LIMIT_MAX_ATTEMPTS = 8;
const EXPORT_GIF_SIZE_LIMIT_MIN_FRAMES = 4;
const EXPORT_GIF_ENCODER_DEFAULT_FRAME_BUDGET_BYTES = 160 * 1024 * 1024;
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
const RUNTIME_ASSET_REVISION = "20260721-optimization-closeout-v1";
const GIF_JS_LIBRARY_URL = `gif.js?v=${RUNTIME_ASSET_REVISION}`;
const GIF_JS_WORKER_URL = `gif.worker.js?v=${RUNTIME_ASSET_REVISION}`;
const GIFUCT_MODULE_URL = `./gifuct-js.bundle.mjs?v=${RUNTIME_ASSET_REVISION}`;
const GIF_INSPECT_WORKER_URL = `./gif-inspect-worker.js?v=${RUNTIME_ASSET_REVISION}`;
const SCENE_RENDER_WORKER_URL = `./scene-render-worker.js?v=${RUNTIME_ASSET_REVISION}`;
const SESSION_SERIALIZE_WORKER_URL = `./session-serialize-worker.js?v=${RUNTIME_ASSET_REVISION}`;
const EXPORT_RASTER_WORKER_URL = `./export-raster-worker.js?v=${RUNTIME_ASSET_REVISION}`;
const EXPORT_RASTER_PROTOCOL = "brush-export-raster";
const EXPORT_RASTER_VERSION = 1;
const EXPORT_RASTER_STARTUP_TIMEOUT_MS = 6000;
const EXPORT_RASTER_PREPARE_TIMEOUT_MS = 180000;
const EXPORT_RASTER_FRAME_TIMEOUT_MS = 60000;
const EXPORT_SOURCE_LOAD_TIMEOUT_MS = 15000;
const EXPORT_SOURCE_CANCEL_POLL_MS = 50;
const EXPORT_SOURCE_IMAGE_CACHE_LIMIT = 64;
const SAVED_PREVIEW_FRAME_TIME_MS = 100;
const EXPORT_MIN_DIMENSION = 1;
const EXPORT_MAX_DIMENSION = 10000;
const EXPORT_SCALE_PRESETS = [5, 10, 25, 50, 100, 200];
const BRUSH_CROP_MIN_SIZE = 4;
const BRUSH_CROP_ZOOM_MIN_PERCENT = 25;
const BRUSH_CROP_ZOOM_MAX_PERCENT = 400;
const BRUSH_CROP_ZOOM_STEP_PERCENT = 25;
const BRUSH_CROP_PREVIEW_MAX_WIDTH = 580;
const BRUSH_CROP_PREVIEW_MAX_HEIGHT = 700;
const BRUSH_CROP_PREVIEW_VIEWPORT_HEIGHT_RATIO = 0.62;
const GIF_TRANSPARENT_MATTE = "#00ff01";
const GIF_TRANSPARENT_MATTE_HEX = 0x00ff01;
const STAMP_INDEX_CELL_SIZE = 256;
const STAMP_VIEWPORT_CULL_MARGIN_PX = 640;
const STAMP_VIEWPORT_HIDE_MARGIN_PX = 1800;
const TRANSPARENT_STAMP_SRC =
  "data:image/gif;base64,R0lGODlhAQABAIAAAAAAAP///ywAAAAAAQABAAACAUwAOw==";
const ERASER_SAMPLE_GRID_SIZE = 5;
const ERASER_PATH_STEP_FACTOR = 0.6;
const ERASER_PATH_MIN_STEP = 6;
const ERASER_MAX_SAMPLES_PER_FRAME = 24;
const EDIT_LAYER_OPAQUE_HIT_BUFFER_PX = 5;
const SPRAY_MIN_STAMPS = 3;
const SPRAY_MAX_STAMPS = 34;
const DEFAULT_SPRAY_SPREAD = 256;
const SHAPE_DRAG_THRESHOLD_PX = 5;
const PLACEMENT_CANCEL_CHECK_INTERVAL = 40;
const EXPORT_CANCEL_CHECK_INTERVAL = 40;
const BRUSH_FRAME_COUNT_DECODE_CONCURRENCY = 2;
const GIF_INSPECT_WORKER_MAX_INPUT_BYTES = 128 * 1024 * 1024;
const GIF_INSPECT_MAIN_FALLBACK_MAX_INPUT_BYTES = 16 * 1024 * 1024;
const GIF_INSPECT_MAIN_FALLBACK_MAX_FRAMES = 20000;
const SEQUENCE_INTERRUPT_TWEEN_MS = 160;
const SEQUENCE_TRIGGER_PRIME_MS = 16;
const SEQUENCE_DATASET_KEYS = [
  "sequenceActive",
  "sequenceBaseOpacity",
  "sequenceBaseSrc",
  "sequenceBaseImageRendering",
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
  "sequenceColorShifted",
  "sequencePixelateStart",
  "sequencePixelateFrom",
  "sequencePixelateTo",
  "sequencePixelateDuration",
  "sequencePixelateTarget",
  "sequencePixelated",
  "sequenceBlurStart",
  "sequenceBlurFrom",
  "sequenceBlurTo",
  "sequenceBlurDuration",
  "sequenceBlurTarget",
  "sequenceBlurred"
];
const SEQUENCE_BASE_DATASET_KEYS = [
  "sequenceActive",
  "sequenceBaseOpacity",
  "sequenceBaseSrc",
  "sequenceBaseImageRendering"
];
const SEQUENCE_SLOT_STATE_KEYS = SEQUENCE_DATASET_KEYS.filter(
  (key) => !SEQUENCE_BASE_DATASET_KEYS.includes(key)
);
const layerSequencePreviewRuntimeByStroke = new WeakMap();
const sequenceSlotRuntimeStampCache = new WeakMap();
const pendingLayerSequenceRefreshByStroke = new Map();
const layerSequencePreviewReducedMotionQuery = typeof window.matchMedia === "function"
  ? window.matchMedia("(prefers-reduced-motion: reduce)")
  : null;

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
  layerMoveHistory: [],
  layerMoveRedoHistory: [],
  nextKeyboardHistoryOrder: 1,
  nextKeyboardUndoOrder: 1,
  sequenceRafId: null,
  sequenceLastFrameTime: null,
  sequencePreviewLastPaintTime: null,
  sequenceActiveStrokeIds: new Set(),
  selectedEditLayerId: null,
  strokeById: new Map(),
  stampSpatialBuckets: new Map(),
  stampSpatialCells: new WeakMap(),
  viewportRenderedStamps: new Set(),
  occlusionCulledStamps: new Set(),
  stampOcclusionIdleId: null,
  stampCount: 0,
  stampVisibilityRafId: null,
  urlRefCounts: new Map(),
  nextBrushId: 1,
  nextStrokeId: 1,
  saveTimerId: null,
  saveIdleCallbackId: null,
  saveRevision: 0,
  savedRevision: 0,
  saveInFlight: false,
  saveUrgentPending: false,
  saveUrgentMicrotaskQueued: false,
  saveUrgentTimerId: null,
  saveUrgentLastStartedAt: -Infinity,
  saveEpoch: 0,
  saveFailureCount: 0,
  sceneRendererActive: false,
  sceneRendererPreparing: false,
  sceneRendererDisabled: false,
  sceneRenderRevision: 0,
  sceneMutationRevision: 0,
  sceneRendererSyncRafId: null,
  sceneRendererElementSyncRafId: null,
  sceneRendererPendingElements: new Set(),
  sceneRendererLastCameraChangeAt: 0,
  soloBrushId: null,
  selectedBrushIds: new Set(),
  brushPickMode: false,
  pendingBrushGallerySelectionScroll: false,
  favoriteBrushSources: new Set(),
  favoriteReturnState: null,
  customBrushPresetSources: Array.from({ length: 5 }, () => new Set()),
  activeCustomBrushPresetIndex: null,
  activeStockBrushFolderId: null,
  activeStockBrushFolderIds: new Set(),
  browsingAllStockBrushes: false,
  stockBrushLoadingFolderId: null,
  gifAnimationsPaused: false,
  sidebarCollapsed: false,
  sidebarTab: "draw",
  previousSidebarTab: "draw",
  brushGalleryCollapsed: false,
  brushGallerySort: DEFAULT_BRUSH_GALLERY_SORT,
  brushGallerySearch: "",
  brushTagMenuOpen: false,
  brushGalleryRandomSeed: createBrushGalleryRandomSeed(),
  brushGalleryPage: 0,
  savedCompositions: [],
  savedCompositionsLoaded: false,
  pendingSavedCompositionDeleteId: null,
  canvasBackgroundColor: "#ffffff",
  exportBackgroundEnabled: true,
  exportSeeBeyondEnabled: true,
  exportGuidelinesEnabled: false,
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
  randomSizeEnabled: false,
  randomSizePercentMin: 75,
  randomSizePercentMax: 125,
  randomSizeFixedMin: 72,
  randomSizeFixedMax: 120,
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
  exportSequencePrewarmSeconds: 0,
  exportGifSizeLimitEnabled: false,
  exportVideoAuto: true,
  exportVideoSeconds: 3,
  exportSelectionBounds: null,
  exportScalePercent: 100,
  exportResolutionLocked: true,
  exportCustomResolution: null,
  exportDrag: null,
  exportCropHistory: [],
  exportCropRedoHistory: [],
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
    zoomPercent: 100,
    weightMode: "normal",
    cropRect: null,
    drag: null
  }
};

let snapshotDbPromise = null;
let snapshotDbConnection = null;
let sessionTabIdCache = null;
let lastLifecycleFlushRevision = -1;
let sessionSerializerWorker = null;
let sessionSerializerRequestId = 0;
const sessionSerializerRequests = new Map();
const sessionStrokeTokenByObject = new WeakMap();
const sessionSerializerAcknowledgedRevisions = new Map();
let nextSessionStrokeToken = 1;
let gifInspectWorker = null;
let gifInspectRequestId = 0;
const gifInspectRequests = new Map();
let sceneRendererWorker = null;
let sceneRendererInitialized = false;
let sceneRendererInitPromise = null;
let sceneRendererInitResolve = null;
let sceneRendererInitReject = null;
const sceneRendererSceneRequests = new Map();
const sceneRendererUpsertRequests = new Map();
const sceneRendererReadySources = new Set();
const sceneRendererUnsupportedSources = new Set();
const sceneStampIdMap = new WeakMap();
const sceneRendererPendingStampRevision = new WeakMap();
let nextSceneStampId = 1;
let brushByIdCacheSource = null;
let brushByIdCacheLength = -1;
let brushByIdCache = new Map();
let brushChoiceCacheRevision = 0;
let brushChoicePoolCache = null;
let sceneRendererCameraIdleTimerId = null;
let nextExportRasterSessionId = 1;
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
    rasterSession: null,
    cancel() {
      this.cancelled = true;
      this.rasterSession?.cancel();
      if (this.gif && typeof this.gif.abort === "function") {
        try {
          this.gif.abort();
        } catch (error) {
          // GIF may already have finished or aborted.
        }
        releaseGifEncoderFrames(this.gif);
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
const pixelateFilterCache = new Map();
const sequencePixelateProxyMap = new WeakMap();
let exportTintScratchCanvas = null;
let exportLayerScratchCanvas = null;
let exportPixelateScratchCanvas = null;
const exportSourceImageCache = new Map();
const exportBackgroundImageCache = new Map();
const exportBackgroundAnimationCache = new Map();
const exportBackgroundStillPreviewCache = new Map();
const exportBackgroundRenderCache = new Map();
const brushSourceDataCache = new Map();
const stockBrushIconPaths = new Map();
let stockBrushCategoryTagsBySource = null;
let stockBrushSourceInfoByLookupKey = null;
let stockBrushMetadataBySource = null;
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

function isNearlyBlackHexColor(hexColor) {
  const { red, green, blue } = hexToRgbUnit(hexColor);
  const luminance = red * 0.2126 + green * 0.7152 + blue * 0.0722;
  return luminance <= 0.22;
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

function getPixelateFilterId(amount) {
  const pixelSize = clamp(Math.round(Number(amount) || 0), 1, 80);
  if (pixelateFilterCache.has(pixelSize)) {
    return pixelateFilterCache.get(pixelSize);
  }

  const filterId = `sequencePixelateFilter-${pixelSize}`;
  const existingFilter = document.getElementById(filterId);
  if (existingFilter) {
    pixelateFilterCache.set(pixelSize, filterId);
    return filterId;
  }

  const defs = filterDefs ? filterDefs.querySelector("defs") : null;
  if (!defs) {
    return "";
  }

  const svgNamespace = "http://www.w3.org/2000/svg";
  const filterElement = document.createElementNS(svgNamespace, "filter");
  filterElement.setAttribute("id", filterId);
  filterElement.setAttribute("x", "-10%");
  filterElement.setAttribute("y", "-10%");
  filterElement.setAttribute("width", "120%");
  filterElement.setAttribute("height", "120%");
  filterElement.setAttribute("primitiveUnits", "userSpaceOnUse");
  filterElement.setAttribute("color-interpolation-filters", "sRGB");

  const dotSize = 1;
  const radius = Math.max(1, Math.floor(pixelSize / 2));

  const flood = document.createElementNS(svgNamespace, "feFlood");
  flood.setAttribute("x", String(Math.max(0, Math.round(pixelSize / 2 - dotSize / 2))));
  flood.setAttribute("y", String(Math.max(0, Math.round(pixelSize / 2 - dotSize / 2))));
  flood.setAttribute("width", String(dotSize));
  flood.setAttribute("height", String(dotSize));
  flood.setAttribute("flood-color", "#000");
  flood.setAttribute("result", "pixelSeed");

  const seed = document.createElementNS(svgNamespace, "feComposite");
  seed.setAttribute("in", "pixelSeed");
  seed.setAttribute("in2", "SourceGraphic");
  seed.setAttribute("operator", "in");
  seed.setAttribute("x", "0");
  seed.setAttribute("y", "0");
  seed.setAttribute("width", String(pixelSize));
  seed.setAttribute("height", String(pixelSize));
  seed.setAttribute("result", "sampledPixel");

  const tile = document.createElementNS(svgNamespace, "feTile");
  tile.setAttribute("in", "sampledPixel");
  tile.setAttribute("result", "pixelGrid");

  const masked = document.createElementNS(svgNamespace, "feComposite");
  masked.setAttribute("in", "SourceGraphic");
  masked.setAttribute("in2", "pixelGrid");
  masked.setAttribute("operator", "in");
  masked.setAttribute("result", "sampledSource");

  const morphology = document.createElementNS(svgNamespace, "feMorphology");
  morphology.setAttribute("in", "sampledSource");
  morphology.setAttribute("operator", "dilate");
  morphology.setAttribute("radius", String(radius));
  morphology.setAttribute("result", "pixelated");

  filterElement.appendChild(flood);
  filterElement.appendChild(seed);
  filterElement.appendChild(tile);
  filterElement.appendChild(masked);
  filterElement.appendChild(morphology);
  defs.appendChild(filterElement);
  pixelateFilterCache.set(pixelSize, filterId);
  return filterId;
}

function getSequenceEffectCssFilter(effects = null) {
  if (!effects || typeof effects !== "object") {
    return "";
  }
  const parts = [];
  const useSvgPixelate = effects.livePixelateSvg === true;
  const pixelateAmount = useSvgPixelate
    ? clamp(Math.round(Number(effects.pixelateAmount) || 0), 0, 64)
    : 0;
  if (useSvgPixelate && pixelateAmount > 0) {
    const pixelateFilterId = getPixelateFilterId(pixelateAmount);
    if (pixelateFilterId) {
      parts.push(`url(#${pixelateFilterId})`);
    }
  }
  const blurAmount = clamp(Number(effects.blurAmount) || 0, 0, 64);
  if (blurAmount > 0) {
    parts.push(`blur(${Math.max(0, blurAmount).toFixed(2)}px)`);
  }
  return parts.join(" ");
}

function applyBrushTintStyle(element, disabled = false, tintSettings = null, effects = null) {
  if (!element) {
    return;
  }
  const filterValue = [getBrushTintCssFilter(disabled, tintSettings), getSequenceEffectCssFilter(effects)]
    .filter(Boolean)
    .join(" ");
  if (filterValue) {
    if (element.style.filter !== filterValue) {
      element.style.filter = filterValue;
    }
  } else if (element.style.filter) {
    element.style.removeProperty("filter");
  }
}

function setInlineStyleIfChanged(element, property, value) {
  if (element?.style?.[property] !== value) {
    element.style[property] = value;
  }
}

function getSequencePixelateProxy(stamp) {
  if (!(stamp instanceof HTMLImageElement)) {
    return null;
  }
  let proxy = sequencePixelateProxyMap.get(stamp);
  if (proxy && proxy.parentElement) {
    return proxy;
  }
  proxy = document.createElement("canvas");
  proxy.className = "sequence-pixelate-proxy";
  proxy.setAttribute("aria-hidden", "true");
  sequencePixelateProxyMap.set(stamp, proxy);
  if (stamp.parentElement) {
    stamp.after(proxy);
  }
  return proxy;
}

function removeSequencePixelateProxy(stamp) {
  const proxy = sequencePixelateProxyMap.get(stamp);
  if (proxy) {
    proxy.remove();
    sequencePixelateProxyMap.delete(stamp);
  }
  if (
    stamp instanceof HTMLElement &&
    stamp.classList.contains("has-sequence-pixelate-proxy")
  ) {
    stamp.classList.remove("has-sequence-pixelate-proxy");
  }
}

function syncSequencePixelateProxy(stamp, visual) {
  const pixelateAmount = clamp(Math.round(Number(visual?.pixelateAmount) || 0), 0, 64);
  if (!(stamp instanceof HTMLImageElement) || pixelateAmount <= 0) {
    removeSequencePixelateProxy(stamp);
    return false;
  }
  const width = Math.max(1, Math.ceil(parseFloat(stamp.style.width) || stamp.naturalWidth || 1));
  const height = Math.max(1, Math.ceil(parseFloat(stamp.style.height) || stamp.naturalHeight || 1));
  const proxy = getSequencePixelateProxy(stamp);
  if (!proxy) {
    return false;
  }
  const pixelWidth = Math.max(1, Math.ceil(width / pixelateAmount));
  const pixelHeight = Math.max(1, Math.ceil(height / pixelateAmount));
  if (proxy.width !== pixelWidth) {
    proxy.width = pixelWidth;
  }
  if (proxy.height !== pixelHeight) {
    proxy.height = pixelHeight;
  }

  const proxyCtx = proxy.getContext("2d", { alpha: true });
  if (!proxyCtx) {
    removeSequencePixelateProxy(stamp);
    return false;
  }
  try {
    proxyCtx.clearRect(0, 0, pixelWidth, pixelHeight);
    proxyCtx.globalAlpha = 1;
    proxyCtx.globalCompositeOperation = "source-over";
    proxyCtx.imageSmoothingEnabled = false;
    proxyCtx.drawImage(stamp, 0, 0, pixelWidth, pixelHeight);
  } catch (error) {
    removeSequencePixelateProxy(stamp);
    return false;
  }

  proxy.style.left = stamp.style.left;
  proxy.style.top = stamp.style.top;
  proxy.style.width = stamp.style.width;
  proxy.style.height = stamp.style.height;
  proxy.style.transform = stamp.style.transform;
  proxy.style.mixBlendMode = stamp.style.mixBlendMode;
  proxy.style.opacity = String(clamp(Number(visual?.opacity) || 0, 0, 1));
  proxy.classList.toggle("is-culled", stamp.classList.contains("is-culled"));
  proxy.classList.toggle("is-layer-hidden", stamp.classList.contains("is-layer-hidden"));
  applyBrushTintStyle(proxy, false, visual?.tintSettings || NO_TINT_SETTINGS, {
    blurAmount: Number(visual?.blurAmount) || 0
  });
  stamp.classList.add("has-sequence-pixelate-proxy");
  return true;
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

function updateBrushGalleryMeta(brush) {
  if (!brushGallery || !brush || state.sidebarTab !== "brushes") {
    return;
  }
  const brushId = Number(brush.id);
  if (!Number.isFinite(brushId)) {
    return;
  }
  const meta = brushGallery.querySelector(
    `.brush-item[data-brush-id="${brushId}"] .brush-meta`
  );
  if (meta) {
    meta.textContent = getBrushMetaText(brush);
  }
}

function createGifInspectClientError(
  code,
  message,
  { category = "internal", retriable = false, details = null, name = "Error" } = {}
) {
  const error = new Error(message || "GIF inspection failed.");
  error.name = name;
  error.code = code || "GIF_INSPECTION_FAILED";
  error.category = category;
  error.retriable = retriable === true;
  if (details && typeof details === "object") {
    error.details = details;
  }
  return error;
}

function createGifInspectWorkerError(payload = null) {
  const errorPayload = payload && typeof payload === "object" ? payload : {};
  return createGifInspectClientError(
    errorPayload.code || "GIF_INSPECTION_FAILED",
    errorPayload.message || "GIF inspection failed.",
    {
      category: errorPayload.category || "internal",
      retriable: errorPayload.retriable === true,
      details: errorPayload.details || null,
    }
  );
}

function isGifInspectCapabilityError(error) {
  return (
    error?.category === "capability" ||
    [
      "GIF_INSPECT_WORKER_UNAVAILABLE",
      "GIF_INSPECT_WORKER_FAILED",
      "GIF_INSPECT_WORKER_POST_FAILED",
      "UNSUPPORTED_VERSION",
    ].includes(String(error?.code || ""))
  );
}

function createGifInspectSafetyError(code, message, details = null) {
  return createGifInspectClientError(code, message, {
    category: "safety",
    details,
  });
}

function disposeGifInspectWorker(error = null) {
  if (gifInspectWorker) {
    gifInspectWorker.terminate();
    gifInspectWorker = null;
  }
  if (error) {
    for (const request of gifInspectRequests.values()) {
      request.reject(error);
    }
  }
  gifInspectRequests.clear();
}

function getGifInspectWorker() {
  if (gifInspectWorker || typeof Worker !== "function") {
    return gifInspectWorker;
  }
  try {
    const worker = new Worker(GIF_INSPECT_WORKER_URL, { type: "module" });
    worker.addEventListener("message", (event) => {
      const message = event.data || {};
      if (message.protocol !== "gif-inspect" || message.version !== 1) {
        return;
      }
      const request = gifInspectRequests.get(message.jobId);
      if (!request || !["result", "error", "cancelled"].includes(message.type)) {
        return;
      }
      gifInspectRequests.delete(message.jobId);
      if (message.type === "result") {
        request.resolve(message.result);
      } else if (message.type === "cancelled") {
        request.reject(
          createGifInspectClientError("GIF_INSPECTION_CANCELLED", "GIF inspection cancelled.", {
            category: "cancelled",
            name: "AbortError",
          })
        );
      } else {
        request.reject(createGifInspectWorkerError(message.error));
      }
    });
    worker.addEventListener("error", () => {
      disposeGifInspectWorker(
        createGifInspectClientError(
          "GIF_INSPECT_WORKER_FAILED",
          "GIF inspection worker failed.",
          { category: "capability" }
        )
      );
    });
    gifInspectWorker = worker;
  } catch (error) {
    gifInspectWorker = null;
  }
  return gifInspectWorker;
}

function inspectGifSourceInWorker(sourceUrl, options = {}) {
  const worker = getGifInspectWorker();
  if (!worker) {
    return {
      jobId: null,
      promise: Promise.reject(
        createGifInspectClientError(
          "GIF_INSPECT_WORKER_UNAVAILABLE",
          "GIF inspection workers are unavailable.",
          { category: "capability" }
        )
      )
    };
  }
  const jobId = `gif-inspect-${++gifInspectRequestId}`;
  const promise = new Promise((resolve, reject) => {
    gifInspectRequests.set(jobId, { resolve, reject });
    try {
      worker.postMessage({
        protocol: "gif-inspect",
        version: 1,
        type: "inspect",
        jobId,
        source: { url: sourceUrl },
        options
      });
    } catch (error) {
      gifInspectRequests.delete(jobId);
      reject(
        createGifInspectClientError(
          "GIF_INSPECT_WORKER_POST_FAILED",
          error instanceof Error ? error.message : "Could not start GIF inspection.",
          {
            category: "capability",
            details: { cause: error instanceof Error ? error.message : "unknown error" },
          }
        )
      );
    }
  });
  return { jobId, promise };
}

function cancelGifInspection(jobId) {
  if (!jobId || !gifInspectWorker || !gifInspectRequests.has(jobId)) {
    return;
  }
  gifInspectWorker.postMessage({
    protocol: "gif-inspect",
    version: 1,
    type: "cancel",
    jobId
  });
}

function clearBrushFrameCountJobs() {
  for (const token of brushFrameCountPromises.values()) {
    cancelGifInspection(token?.jobId);
    token?.fallbackController?.abort();
  }
  brushFrameCountPromises.clear();
  brushFrameCountQueue.length = 0;
}

async function readGifInspectionFallbackBytes(sourceUrl, maxInputBytes, signal = null) {
  const inputLimit = Math.max(1, Math.floor(Number(maxInputBytes) || 0));
  if (signal?.aborted) {
    throw createCancellationError("GIF inspection cancelled.");
  }
  if (typeof sourceUrl !== "string" || !sourceUrl) {
    throw createGifInspectClientError("INVALID_SOURCE", "Missing GIF source.", {
      category: "input",
    });
  }

  if (sourceUrl.startsWith("data:")) {
    const markerIndex = sourceUrl.indexOf(",");
    if (markerIndex < 0) {
      throw createGifInspectClientError("INVALID_SOURCE", "Invalid GIF data URL.", {
        category: "input",
      });
    }
    const metadata = sourceUrl.slice(0, markerIndex);
    const payloadLength = sourceUrl.length - markerIndex - 1;
    const maximumEncodedLength = metadata.includes(";base64")
      ? Math.ceil(inputLimit * 4 / 3) + 4
      : inputLimit * 3;
    if (payloadLength > maximumEncodedLength) {
      throw createGifInspectSafetyError(
        "INPUT_TOO_LARGE",
        "The GIF exceeds the bounded fallback byte limit.",
        { maxInputBytes: inputLimit }
      );
    }
    const bytes = dataUrlToUint8Array(sourceUrl);
    if (bytes.byteLength > inputLimit) {
      throw createGifInspectSafetyError(
        "INPUT_TOO_LARGE",
        "The GIF exceeds the bounded fallback byte limit.",
        { byteLength: bytes.byteLength, maxInputBytes: inputLimit }
      );
    }
    return bytes;
  }

  let response;
  try {
    response = await fetch(sourceUrl, {
      signal,
      credentials: "same-origin",
    });
  } catch (error) {
    if (signal?.aborted || isCancellationError(error)) {
      throw createCancellationError("GIF inspection cancelled.");
    }
    throw createGifInspectClientError("FETCH_FAILED", "The GIF URL could not be fetched.", {
      category: "network",
      retriable: true,
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }
  if (!response.ok) {
    throw createGifInspectClientError(
      "FETCH_FAILED",
      `The GIF request failed with HTTP ${response.status}.`,
      {
        category: "network",
        retriable: response.status >= 500,
        details: { status: response.status },
      }
    );
  }

  const contentLengthHeader = response.headers.get("content-length");
  const declaredLength = contentLengthHeader == null ? NaN : Number(contentLengthHeader);
  if (Number.isFinite(declaredLength) && declaredLength > inputLimit) {
    await response.body?.cancel?.("GIF input exceeded its bounded fallback byte limit.");
    throw createGifInspectSafetyError(
      "INPUT_TOO_LARGE",
      "The GIF exceeds the bounded fallback byte limit.",
      { byteLength: declaredLength, maxInputBytes: inputLimit }
    );
  }
  if (!response.body?.getReader) {
    throw createGifInspectClientError(
      "GIF_INSPECT_BOUNDED_FALLBACK_UNAVAILABLE",
      "A bounded GIF metadata fallback is unavailable in this browser.",
      { category: "capability" }
    );
  }

  const reader = response.body.getReader();
  const chunks = [];
  let byteLength = 0;
  try {
    while (true) {
      if (signal?.aborted) {
        throw createCancellationError("GIF inspection cancelled.");
      }
      const { done, value } = await reader.read();
      if (done) {
        break;
      }
      byteLength += value.byteLength;
      if (byteLength > inputLimit) {
        await reader.cancel("GIF input exceeded its bounded fallback byte limit.");
        throw createGifInspectSafetyError(
          "INPUT_TOO_LARGE",
          "The GIF exceeds the bounded fallback byte limit.",
          { byteLength, maxInputBytes: inputLimit }
        );
      }
      chunks.push(value);
    }
  } finally {
    reader.releaseLock();
  }

  const bytes = new Uint8Array(byteLength);
  let offset = 0;
  for (const chunk of chunks) {
    bytes.set(chunk, offset);
    offset += chunk.byteLength;
  }
  return bytes;
}

async function inspectGifFrameCountOnMainThreadBounded(sourceUrl, signal = null) {
  const bytes = await readGifInspectionFallbackBytes(
    sourceUrl,
    GIF_INSPECT_MAIN_FALLBACK_MAX_INPUT_BYTES,
    signal
  );
  if (bytes.byteLength < 13) {
    throw createGifInspectClientError("INVALID_GIF", "The source is too short to be a GIF.", {
      category: "input",
    });
  }
  const signature = String.fromCharCode(...bytes.subarray(0, 6));
  if (signature !== "GIF87a" && signature !== "GIF89a") {
    throw createGifInspectClientError("INVALID_GIF", "The source is not a GIF.", {
      category: "input",
    });
  }

  const gifuctModule = await loadGifuctModule();
  if (signal?.aborted) {
    throw createCancellationError("GIF inspection cancelled.");
  }
  let parsed;
  try {
    parsed = gifuctModule.parseGIF(
      bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength)
    );
  } catch (error) {
    throw createGifInspectClientError("PARSE_FAILED", "The GIF could not be parsed.", {
      category: "input",
      details: { cause: error instanceof Error ? error.message : "unknown error" },
    });
  }
  const frameCount = Array.isArray(parsed?.frames)
    ? parsed.frames.reduce((count, frame) => count + (frame?.image ? 1 : 0), 0)
    : 0;
  if (frameCount <= 0) {
    throw createGifInspectClientError("NO_FRAMES", "The GIF contains no image frames.", {
      category: "input",
    });
  }
  if (frameCount > GIF_INSPECT_MAIN_FALLBACK_MAX_FRAMES) {
    throw createGifInspectSafetyError(
      "GIF_FRAME_LIMIT_EXCEEDED",
      "The GIF exceeds the bounded fallback frame limit.",
      { frameCount, maxFrameCount: GIF_INSPECT_MAIN_FALLBACK_MAX_FRAMES }
    );
  }
  return frameCount;
}

function runBrushFrameCountQueue() {
  while (
    activeBrushFrameCountDecodes < BRUSH_FRAME_COUNT_DECODE_CONCURRENCY &&
    brushFrameCountQueue.length
  ) {
    const job = brushFrameCountQueue.shift();
    activeBrushFrameCountDecodes += 1;

    window.setTimeout(() => {
      if (brushFrameCountPromises.get(job.brushId) !== job.token) {
        activeBrushFrameCountDecodes = Math.max(0, activeBrushFrameCountDecodes - 1);
        runBrushFrameCountQueue();
        return;
      }
      const inspection = inspectGifSourceInWorker(job.sourceUrl, {
        checkOpacity: false,
        maxInputBytes: GIF_INSPECT_WORKER_MAX_INPUT_BYTES,
      });
      job.token.jobId = inspection.jobId;
      inspection.promise
        .then((result) => normalizeBrushFrameCount(result?.frameCount) || 1)
        .catch(async (error) => {
          if (brushFrameCountPromises.get(job.brushId) !== job.token) {
            return null;
          }
          if (isCancellationError(error) || error?.category === "cancelled") {
            return null;
          }
          if (!isGifInspectCapabilityError(error)) {
            return 1;
          }
          const fallbackController = new AbortController();
          job.token.fallbackController = fallbackController;
          try {
            const frameCount = await inspectGifFrameCountOnMainThreadBounded(
              job.sourceUrl,
              fallbackController.signal
            );
            return normalizeBrushFrameCount(frameCount) || 1;
          } catch (error) {
            if (isCancellationError(error) || fallbackController.signal.aborted) {
              return null;
            }
            return 1;
          } finally {
            if (job.token.fallbackController === fallbackController) {
              job.token.fallbackController = null;
            }
          }
        })
        .then((count) => {
          if (!count || brushFrameCountPromises.get(job.brushId) !== job.token) {
            return;
          }
          const currentBrush = findBrushById(job.brushId);
          if (!currentBrush || getBrushOriginalUrl(currentBrush) !== job.sourceUrl) {
            return;
          }
          currentBrush.frameCount = count;
          updateBrushGalleryMeta(currentBrush);
          scheduleSessionSave();
        })
        .finally(() => {
          if (brushFrameCountPromises.get(job.brushId) === job.token) {
            brushFrameCountPromises.delete(job.brushId);
          }
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

  const sourceUrl = getBrushOriginalUrl(brush);
  const token = { jobId: null, fallbackController: null };
  brushFrameCountPromises.set(brushId, token);
  brushFrameCountQueue.push({ brushId, sourceUrl, token });
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

function markGifPlaybackStart(image, source = "", force = false) {
  if (!(image instanceof HTMLImageElement)) {
    return;
  }
  const gifSource = source || getImageGifSource(image);
  if (!isGifUrl(gifSource)) {
    delete image.dataset.gifPlaybackSource;
    delete image.dataset.gifPlaybackStartedAt;
    return;
  }
  if (
    force ||
    image.dataset.gifPlaybackSource !== gifSource ||
    !Number.isFinite(Number(image.dataset.gifPlaybackStartedAt))
  ) {
    image.dataset.gifPlaybackSource = gifSource;
    image.dataset.gifPlaybackStartedAt = String(performance.now());
  }
}

function isViewportCulledStamp(image) {
  return image instanceof HTMLImageElement && image.dataset.viewportCulled === "true";
}

function isOcclusionCulledStamp(image) {
  return image instanceof HTMLImageElement && image.dataset.occlusionCulled === "true";
}

function isRenderCulledStamp(image) {
  return isViewportCulledStamp(image) || isOcclusionCulledStamp(image);
}

function strokeHasActiveSequenceTransform(stroke) {
  return Boolean(
    stroke &&
      !stroke.hidden &&
      isLayerSequenceEnabled(stroke) &&
      getLayerSequenceSlots(stroke).some((slot) =>
        slot && (slot.effect === "move" || slot.effect === "rotate" || slot.effect === "scale")
      )
  );
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
    isRenderCulledStamp(image) ||
    isSceneRendererStampSuppressed(image)
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

  if (isSceneRendererStampSuppressed(image)) {
    markGifPlaybackStart(image, pausedSource);
    delete image.dataset.gifPausedSrc;
    return;
  }

  image.src = pausedSource;
  markGifPlaybackStart(image, pausedSource, true);
  delete image.dataset.gifPausedSrc;
}

function applyGifPauseStateToImage(image) {
  if (shouldPauseGifImage(image)) {
    freezeGifImage(image);
  } else {
    markGifPlaybackStart(image);
  }
}

function applyBrushGalleryPreviewAnimationState(preview, brush, previewDisabledBrush = false) {
  if (!(preview instanceof HTMLImageElement)) {
    return;
  }

  if (brush && brush.enabled === false && !previewDisabledBrush) {
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
  gifPauseButton.classList.toggle(
    "has-light-outline",
    state.showGifPauseButton !== false &&
      ((state.exportMode && state.exportSeeBeyondEnabled === false) ||
        isNearlyBlackHexColor(state.canvasBackgroundColor))
  );
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
  if (state.sceneRendererActive || state.sceneRendererPreparing) {
    deactivateSceneRenderer();
  }
  invalidateStampOcclusion();
  const shouldPause = Boolean(paused);
  const now = performance.now();
  for (const stroke of state.strokes) {
    setStrokeSequenceClockPaused(stroke, shouldPause || Boolean(stroke.animationPaused), now);
  }
  state.gifAnimationsPaused = shouldPause;
  applyGlobalGifPauseState(state.gifAnimationsPaused);
  updateGifPauseButtonUI();
  refreshLayerSequenceLoop();
  if (!state.gifAnimationsPaused) {
    scheduleStampOcclusionRefresh();
  }
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
  const source =
    typeof brush?.originalUrl === "string" && brush.originalUrl
      ? brush.originalUrl
      : typeof brush?.url === "string"
      ? brush.url
      : "";
  return getStockBrushRequestUrl(source);
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

function updateBrushCropTagsUI(brush) {
  if (!brushCropTags) {
    return;
  }
  const tags = getBrushTags(brush);
  brushCropTags.replaceChildren();
  brushCropTags.hidden = tags.length === 0;
  if (!tags.length) {
    return;
  }

  const fragment = document.createDocumentFragment();
  for (const tag of tags) {
    const tagElement = document.createElement("span");
    tagElement.className = "brush-crop-tag";
    tagElement.textContent = `#${tag}`;
    fragment.appendChild(tagElement);
  }
  brushCropTags.appendChild(fragment);
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
  state.brushCropEditor.zoomPercent = 100;
  clearBrushCropFramePreviewTimer();
  state.brushCropEditor.weightMode = normalizeBrushWeightMode(brush.weightMode);
  state.brushCropEditor.cropRect = currentCrop;
  state.brushCropEditor.drag = null;
  brushCropConfirmButton.disabled = false;
  brushCropCancelButton.disabled = false;
  brushCropModal.classList.add("is-open");
  brushCropModal.setAttribute("aria-hidden", "false");
  updateBrushCropZoomUI();
  applyBrushCropPreviewSize();
  if (brushCropStageWrap) {
    brushCropStageWrap.scrollLeft = 0;
    brushCropStageWrap.scrollTop = 0;
  }
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
  updateBrushCropTagsUI(brush);
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
  state.brushCropEditor.zoomPercent = 100;
  state.brushCropEditor.weightMode = "normal";
  state.brushCropEditor.cropRect = null;
  state.brushCropEditor.drag = null;
  brushCropModal.classList.remove("is-open");
  brushCropModal.setAttribute("aria-hidden", "true");
  if (brushCropTags) {
    brushCropTags.replaceChildren();
    brushCropTags.hidden = true;
  }
  updateBrushCropZoomUI();
  brushCropImage.style.width = "";
  brushCropImage.style.height = "";
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

function normalizeBrushCropZoomPercent(value) {
  const numericValue = Number(value);
  if (!Number.isFinite(numericValue)) {
    return 100;
  }
  const steppedValue = Math.round(numericValue / BRUSH_CROP_ZOOM_STEP_PERCENT) *
    BRUSH_CROP_ZOOM_STEP_PERCENT;
  return clamp(steppedValue, BRUSH_CROP_ZOOM_MIN_PERCENT, BRUSH_CROP_ZOOM_MAX_PERCENT);
}

function updateBrushCropZoomUI() {
  const zoomPercent = normalizeBrushCropZoomPercent(state.brushCropEditor.zoomPercent);
  state.brushCropEditor.zoomPercent = zoomPercent;
  if (brushCropZoomInput) {
    brushCropZoomInput.value = String(zoomPercent);
    brushCropZoomInput.setAttribute("aria-valuetext", `${zoomPercent}%`);
  }
  if (brushCropZoomReadout) {
    brushCropZoomReadout.textContent = `${zoomPercent}%`;
  }
  if (brushCropZoomOutButton) {
    brushCropZoomOutButton.disabled = zoomPercent <= BRUSH_CROP_ZOOM_MIN_PERCENT;
  }
  if (brushCropZoomInButton) {
    brushCropZoomInButton.disabled = zoomPercent >= BRUSH_CROP_ZOOM_MAX_PERCENT;
  }
}

function getBrushCropBasePreviewSize() {
  const fullWidth = Math.max(1, Number(state.brushCropEditor.imageWidth) || 1);
  const fullHeight = Math.max(1, Number(state.brushCropEditor.imageHeight) || 1);
  const viewportWidth = Math.max(1, window.innerWidth - 62);
  const stageWrapWidth = Math.max(
    1,
    (Number(brushCropStageWrap?.clientWidth) || viewportWidth) - 16
  );
  const maxWidth = Math.max(
    1,
    Math.min(BRUSH_CROP_PREVIEW_MAX_WIDTH, viewportWidth, stageWrapWidth)
  );
  const maxHeight = Math.max(
    1,
    Math.min(
      BRUSH_CROP_PREVIEW_MAX_HEIGHT,
      window.innerHeight * BRUSH_CROP_PREVIEW_VIEWPORT_HEIGHT_RATIO
    )
  );
  const fitScale = Math.min(1, maxWidth / fullWidth, maxHeight / fullHeight);
  return {
    width: fullWidth * fitScale,
    height: fullHeight * fitScale
  };
}

function applyBrushCropPreviewSize() {
  if (!brushCropImage) {
    return;
  }
  const baseSize = getBrushCropBasePreviewSize();
  const zoomScale = normalizeBrushCropZoomPercent(state.brushCropEditor.zoomPercent) / 100;
  brushCropImage.style.width = `${baseSize.width * zoomScale}px`;
  brushCropImage.style.height = `${baseSize.height * zoomScale}px`;
}

function centerBrushCropSelectionInPreview() {
  if (!brushCropStageWrap || !brushCropSelection) {
    return;
  }
  const wrapRect = brushCropStageWrap.getBoundingClientRect();
  const selectionRect = brushCropSelection.getBoundingClientRect();
  brushCropStageWrap.scrollLeft +=
    (selectionRect.left + selectionRect.width / 2) - (wrapRect.left + wrapRect.width / 2);
  brushCropStageWrap.scrollTop +=
    (selectionRect.top + selectionRect.height / 2) - (wrapRect.top + wrapRect.height / 2);
}

function setBrushCropZoomPercent(value) {
  state.brushCropEditor.zoomPercent = normalizeBrushCropZoomPercent(value);
  updateBrushCropZoomUI();
  renderBrushCropModal();
  centerBrushCropSelectionInPreview();
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

  applyBrushCropPreviewSize();

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
    request.onsuccess = () => {
      snapshotDbConnection = request.result;
      snapshotDbConnection.addEventListener("versionchange", () => {
        snapshotDbConnection?.close();
        snapshotDbConnection = null;
        snapshotDbPromise = null;
      }, { once: true });
      resolve(snapshotDbConnection);
    };
    request.onerror = () => {
      snapshotDbPromise = null;
      reject(request.error || new Error("Failed to open snapshot DB"));
    };
  });

  return snapshotDbPromise;
}

function beginSnapshotWriteToIndexedDb(database, tabId, snapshotJson) {
  return new Promise((resolve, reject) => {
    let transaction;
    try {
      transaction = database.transaction(SESSION_IDB_STORE_NAME, "readwrite");
      transaction.objectStore(SESSION_IDB_STORE_NAME).put(snapshotJson, tabId);
    } catch (error) {
      reject(error);
      return;
    }
    transaction.oncomplete = () => resolve();
    transaction.onerror = () => reject(transaction.error || new Error("Snapshot write failed"));
    transaction.onabort = () => reject(transaction.error || new Error("Snapshot write aborted"));
  });
}

async function writeSnapshotToIndexedDb(tabId, snapshotJson) {
  const database = await openSnapshotDb();
  await beginSnapshotWriteToIndexedDb(database, tabId, snapshotJson);
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

function getLifecycleSnapshotKeyFromPointer(pointer) {
  const value = String(pointer || "");
  if (!value.startsWith(SESSION_IDB_PREFIX)) {
    return "";
  }
  const key = value.slice(SESSION_IDB_PREFIX.length);
  return key.includes(":lifecycle:") ? key : "";
}

function cleanupSupersededLifecycleSnapshot(pointer, preservedKey = "") {
  const key = getLifecycleSnapshotKeyFromPointer(pointer);
  if (!key || key === preservedKey) {
    return;
  }
  void deleteSnapshotFromIndexedDb(key).catch(() => {
    // Lifecycle cleanup is opportunistic and must never invalidate a good save.
  });
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
  return getCanonicalStockBrushSource(brush?.originalUrl || brush?.url || "");
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
        ? parsed.map(getCanonicalStockBrushSource).filter(Boolean)
        : []
    );
    saveFavoriteBrushSources();
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
  const normalized = getCanonicalStockBrushSource(source);
  return Boolean(normalized && state.favoriteBrushSources instanceof Set && state.favoriteBrushSources.has(normalized));
}

function isBrushFavorite(brush) {
  return isBrushSourceFavorite(getBrushFavoriteSource(brush));
}

function getBrushPresetSource(brush) {
  return getCanonicalStockBrushSource(brush?.originalUrl || brush?.url || "");
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
    return new Set(sources.map(getCanonicalStockBrushSource).filter(Boolean));
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
  const normalized = getCanonicalStockBrushSource(source);
  return Boolean(normalized && getCustomBrushPresetSources(presetIndex).has(normalized));
}

function clearActiveCustomBrushPreset() {
  state.activeCustomBrushPresetIndex = null;
}

function setActiveStockBrushFolders(folderIds, mode = "multi") {
  const validIds = Array.from(new Set(
    (Array.isArray(folderIds) ? folderIds : [folderIds])
      .map(normalizeStockBrushFolderId)
      .filter((folderId) => getStockBrushFolderById(folderId))
  ));
  state.browsingAllStockBrushes = false;
  state.activeStockBrushFolderIds = new Set(validIds);
  if (!validIds.length) {
    state.activeStockBrushFolderId = null;
  } else if (validIds.length === 1 && mode !== "multi") {
    state.activeStockBrushFolderId = validIds[0];
  } else {
    state.activeStockBrushFolderId = mode === "all" ? "all" : validIds.length === 1 ? validIds[0] : "multi";
  }
}

function clearActiveStockBrushFolders() {
  state.browsingAllStockBrushes = false;
  state.activeStockBrushFolderId = null;
  state.activeStockBrushFolderIds = new Set();
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
    resetBrushGalleryForBrushSetChange();
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    clearActiveStockBrushFolders();
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
    tags: getBrushTags(brush),
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
    activeStockBrushFolderIds: Array.from(getActiveStockBrushFolderIdSet()),
    browsingAllStockBrushes: state.browsingAllStockBrushes,
    sidebarTab: state.sidebarTab,
    previousSidebarTab: state.previousSidebarTab,
    sidebarCollapsed: state.sidebarCollapsed,
    brushGalleryCollapsed: state.brushGalleryCollapsed,
    brushGallerySort: state.brushGallerySort,
    brushGallerySearch: state.brushGallerySearch,
    brushGalleryRandomSeed: state.brushGalleryRandomSeed,
    brushGalleryPage: state.brushGalleryPage
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
  if (
    snapshot.activeStockBrushFolderId !== "all" &&
    Array.isArray(snapshot.activeStockBrushFolderIds) &&
    snapshot.activeStockBrushFolderIds.length
  ) {
    setActiveStockBrushFolders(snapshot.activeStockBrushFolderIds);
  } else if (typeof snapshot.activeStockBrushFolderId === "string" && snapshot.activeStockBrushFolderId) {
    if (snapshot.activeStockBrushFolderId === "all") {
      setActiveStockBrushFolders(
        getOrderedStockBrushFolders()
          .filter((folder) => getStockBrushFiles(folder).length)
          .map((folder) => folder.id),
        "all"
      );
    } else if (getStockBrushFolderById(snapshot.activeStockBrushFolderId)) {
      setActiveStockBrushFolders([snapshot.activeStockBrushFolderId], "single");
    } else {
      clearActiveStockBrushFolders();
      state.activeStockBrushFolderId = snapshot.activeStockBrushFolderId === "favorites" ? "favorites" : null;
    }
  } else {
    clearActiveStockBrushFolders();
  }
  state.browsingAllStockBrushes = Boolean(snapshot.browsingAllStockBrushes);
  state.sidebarTab = normalizeSidebarTab(snapshot.sidebarTab);
  state.previousSidebarTab = normalizeSidebarTab(snapshot.previousSidebarTab);
  state.sidebarCollapsed = Boolean(snapshot.sidebarCollapsed);
  state.brushGalleryCollapsed = Boolean(snapshot.brushGalleryCollapsed);
  state.brushGallerySort = normalizeBrushGallerySort(snapshot.brushGallerySort);
  state.brushGallerySearch = normalizeBrushGallerySearch(snapshot.brushGallerySearch);
  state.brushGalleryRandomSeed =
    normalizeBrushGalleryRandomSeed(snapshot.brushGalleryRandomSeed) ?? createBrushGalleryRandomSeed();
  state.brushGalleryPage = normalizeBrushGalleryPage(snapshot.brushGalleryPage);
  if (state.brushGallerySort === "random") {
    resetBrushGalleryForBrushSetChange();
  }
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
  if (
    brushByIdCacheSource !== state.brushes ||
    brushByIdCacheLength !== state.brushes.length
  ) {
    brushByIdCacheSource = state.brushes;
    brushByIdCacheLength = state.brushes.length;
    brushByIdCache = new Map(state.brushes.map((brush) => [brush.id, brush]));
  }
  return brushByIdCache.get(id) || null;
}

function invalidateBrushChoicePool() {
  brushChoiceCacheRevision += 1;
  brushChoicePoolCache = null;
}

function getSoloBrush() {
  if (!Number.isFinite(Number(state.soloBrushId))) {
    return null;
  }
  const brush = findBrushById(Number(state.soloBrushId));
  if (!brush) {
    state.soloBrushId = null;
    invalidateBrushChoicePool();
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
    invalidateBrushChoicePool();
  }

  return selectedBrushes;
}

function clearSelectedBrushes() {
  if (state.selectedBrushIds instanceof Set) {
    state.selectedBrushIds.clear();
  } else {
    state.selectedBrushIds = new Set();
  }
  invalidateBrushChoicePool();
}

function setSoloBrushId(brushId) {
  clearSelectedBrushes();
  state.soloBrushId = Number.isFinite(Number(brushId)) ? Number(brushId) : null;
  invalidateBrushChoicePool();
}

function updateBrushImagePickerButton() {
  if (!brushImagePickerButton) {
    return;
  }
  brushImagePickerButton.classList.toggle("is-active", Boolean(state.brushPickMode));
  brushImagePickerButton.setAttribute("aria-pressed", String(Boolean(state.brushPickMode)));
}

function setBrushPickMode(active) {
  state.brushPickMode = Boolean(active) && state.sidebarTab === "draw";
  if (state.brushPickMode) {
    if (state.sceneRendererActive || state.sceneRendererPreparing) {
      deactivateSceneRenderer();
    }
    if (state.eraseMode) {
      setEraseMode(false);
    }
    cancelShapeDraft();
    hideBrushCursorPreview();
  }
  updateBrushImagePickerButton();
  updateBrushCursorPreview();
  if (!state.brushPickMode) {
    scheduleSceneRendererEvaluation();
  }
}

function updateSliderText() {
  if (isRandomSizeEnabled()) {
    const range = getActiveRandomSizeRange();
    const rangeText = `${Math.round(range.min)}-${Math.round(range.max)}`;
    sizeValue.textContent = rangeText;
    consistentSizeValue.textContent = rangeText;
  } else {
    sizeValue.textContent = String(sizeSlider.value);
    consistentSizeValue.textContent = String(consistentSizeSlider.value);
  }
  spacingValue.textContent = String(getSpacingValue());
  rotationValue.textContent = String(rotationSlider.value);
  opacityValue.textContent = String(opacitySlider.value);
  cursorTrailCountValue.textContent = String(cursorTrailCountSlider.value);
  spraySpreadValue.textContent = String(spraySpreadSlider.value);
  tintAmountValue.textContent = String(tintAmountSlider.value);
  updateRandomSizeRangeFill();
}

function isRandomSizeEnabled() {
  return Boolean(randomSizeToggle && randomSizeToggle.checked);
}

function getRandomSizeLimits(isConsistentMode = consistentToggle.checked) {
  return isConsistentMode
    ? {
        min: Number(consistentSizeSlider.min) || 8,
        max: Number(consistentSizeSlider.max) || 1000
      }
    : {
        min: Number(sizeSlider.min) || 10,
        max: Number(sizeSlider.max) || 1000
      };
}

function getRandomSizeStateKeys(isConsistentMode = consistentToggle.checked) {
  return isConsistentMode
    ? { min: "randomSizeFixedMin", max: "randomSizeFixedMax" }
    : { min: "randomSizePercentMin", max: "randomSizePercentMax" };
}

function normalizeRandomSizeRange(minValue, maxValue, isConsistentMode = consistentToggle.checked) {
  const limits = getRandomSizeLimits(isConsistentMode);
  const rawMin = Number(minValue);
  const rawMax = Number(maxValue);
  const min = clamp(
    Number.isFinite(rawMin) ? rawMin : limits.min,
    limits.min,
    limits.max
  );
  const max = clamp(
    Number.isFinite(rawMax) ? rawMax : limits.max,
    limits.min,
    limits.max
  );
  return {
    min: Math.min(min, max),
    max: Math.max(min, max)
  };
}

function getRandomSizeRangeForMode(isConsistentMode = consistentToggle.checked) {
  const keys = getRandomSizeStateKeys(isConsistentMode);
  return normalizeRandomSizeRange(state[keys.min], state[keys.max], isConsistentMode);
}

function setRandomSizeRangeForMode(minValue, maxValue, isConsistentMode = consistentToggle.checked) {
  const keys = getRandomSizeStateKeys(isConsistentMode);
  const range = normalizeRandomSizeRange(minValue, maxValue, isConsistentMode);
  state[keys.min] = range.min;
  state[keys.max] = range.max;
  return range;
}

function getActiveRandomSizeRange() {
  return getRandomSizeRangeForMode(consistentToggle.checked);
}

function initializeRandomSizeRangeFromCurrent() {
  const isConsistentMode = consistentToggle.checked;
  const limits = getRandomSizeLimits(isConsistentMode);
  const current = isConsistentMode
    ? parseNumericInputValue(consistentSizeSlider, 96)
    : parseNumericInputValue(sizeSlider, 100);
  const spread = Math.max(1, Math.round(current * 0.25));
  setRandomSizeRangeForMode(
    clamp(current - spread, limits.min, limits.max),
    clamp(current + spread, limits.min, limits.max),
    isConsistentMode
  );
}

function syncRandomSizeSlidersFromState() {
  if (!randomSizeMinSlider || !randomSizeMaxSlider) {
    return;
  }
  const limits = getRandomSizeLimits();
  const range = getActiveRandomSizeRange();
  for (const slider of [randomSizeMinSlider, randomSizeMaxSlider]) {
    slider.min = String(limits.min);
    slider.max = String(limits.max);
    slider.step = "1";
    slider.disabled = !isRandomSizeEnabled();
  }
  randomSizeMinSlider.value = String(Math.round(range.min));
  randomSizeMaxSlider.value = String(Math.round(range.max));
}

function updateRandomSizeRangeFill() {
  if (!randomSizeRangeFill || !randomSizeMinSlider || !randomSizeMaxSlider) {
    return;
  }
  const limits = getRandomSizeLimits();
  const range = getActiveRandomSizeRange();
  const span = Math.max(1, limits.max - limits.min);
  const left = ((range.min - limits.min) / span) * 100;
  const right = ((range.max - limits.min) / span) * 100;
  randomSizeRangeFill.style.left = `${clamp(left, 0, 100)}%`;
  randomSizeRangeFill.style.width = `${clamp(right - left, 0, 100)}%`;
}

function readRandomSizeSliders() {
  if (!randomSizeMinSlider || !randomSizeMaxSlider) {
    return;
  }
  setRandomSizeRangeForMode(randomSizeMinSlider.value, randomSizeMaxSlider.value);
  syncRandomSizeSlidersFromState();
  updateSliderText();
  updateEraseCursorGeometry();
  updateBrushCursorPreview();
  scheduleSessionSave();
}

function sampleRandomizedSizeValue(range) {
  const min = Number(range?.min);
  const max = Number(range?.max);
  if (!Number.isFinite(min) || !Number.isFinite(max) || max <= min) {
    return Number.isFinite(min) ? min : 0;
  }
  const safeMin = Math.max(0.001, min);
  const ratio = max / safeMin;
  if (ratio >= 2) {
    return safeMin * Math.pow(ratio, Math.random());
  }
  return min + (max - min) * Math.random();
}

function getBrushSizeFromLongestSide(brush, longestSide) {
  const sourceWidth = Math.max(1, Number(brush?.width) || 1);
  const sourceHeight = Math.max(1, Number(brush?.height) || 1);
  const scale = Math.max(4, Number(longestSide) || 4) / Math.max(sourceWidth, sourceHeight);
  return {
    width: Math.max(4, sourceWidth * scale),
    height: Math.max(4, sourceHeight * scale)
  };
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
  return ["alpha", "random", "area-asc", "area-desc"].includes(sortMode)
    ? sortMode
    : DEFAULT_BRUSH_GALLERY_SORT;
}

function normalizeBrushGallerySearch(value) {
  return typeof value === "string" ? value.slice(0, 160) : "";
}

function createBrushGalleryRandomSeed() {
  try {
    const values = new Uint32Array(1);
    window.crypto.getRandomValues(values);
    return values[0];
  } catch (error) {
    return Math.floor(Math.random() * 0x100000000) >>> 0;
  }
}

function normalizeBrushGalleryRandomSeed(value) {
  const numericSeed = Number(value);
  return Number.isFinite(numericSeed) ? Math.floor(numericSeed) >>> 0 : null;
}

function getBrushGalleryRandomRank(brush, seed) {
  let value = ((Number(brush?.id) >>> 0) ^ seed) >>> 0;
  value = Math.imul(value ^ (value >>> 16), 0x7feb352d);
  value = Math.imul(value ^ (value >>> 15), 0x846ca68b);
  return (value ^ (value >>> 16)) >>> 0;
}

function normalizeBrushGalleryPage(pageIndex) {
  const numericPage = Math.floor(Number(pageIndex));
  return Number.isFinite(numericPage) && numericPage > 0 ? numericPage : 0;
}

function resetBrushGalleryPage() {
  state.brushGalleryPage = 0;
  state.pendingBrushGallerySelectionScroll = false;
}

function resetBrushGalleryForBrushSetChange() {
  resetBrushGalleryPage();
  if (normalizeBrushGallerySort(state.brushGallerySort) === "random") {
    state.brushGalleryRandomSeed = createBrushGalleryRandomSeed();
  }
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
  const randomSizeEnabled = isRandomSizeEnabled();
  state.randomSizeEnabled = randomSizeEnabled;
  sizeSlider.disabled = isConsistentMode || randomSizeEnabled;
  sizeScaleGroup.classList.toggle("is-consistent-size", isConsistentMode);
  sizeScaleGroup.classList.toggle("is-random-size", randomSizeEnabled);
  if (sizeControlLabel) {
    sizeControlLabel.textContent = isConsistentMode ? "size (consistent)" : "size";
  }
  if (sizeControlLabel) {
    sizeControlLabel.setAttribute(
      "for",
      randomSizeEnabled
        ? "randomSizeMinSlider"
        : isConsistentMode
        ? "consistentSizeSlider"
        : "sizeSlider"
    );
  }
  if (sizePercentValueText) {
    sizePercentValueText.hidden = isConsistentMode;
  }
  if (consistentSizeValueText) {
    consistentSizeValueText.hidden = !isConsistentMode;
  }
  if (sizePercentGroup) {
    sizePercentGroup.hidden = isConsistentMode || randomSizeEnabled;
  }
  consistentSizeGroup.hidden = !isConsistentMode || randomSizeEnabled;
  consistentSizeSlider.disabled = !isConsistentMode || randomSizeEnabled;
  if (randomSizeGroup) {
    randomSizeGroup.hidden = !randomSizeEnabled;
  }
  syncRandomSizeSlidersFromState();
  updateSliderText();
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

function getBaseDrawMode(mode) {
  return BASE_DRAW_MODE_BY_OUTLINE.get(mode) || mode;
}

function isOutlineShapeDrawMode(mode) {
  return OUTLINE_SHAPE_DRAW_MODES.has(mode);
}

function getDrawModeButtonLabel(mode, isOutlineVariant = false) {
  if (mode === "pencil") {
    return "Pencil tool";
  }
  if (mode === "spray") {
    return "Spray tool";
  }
  if (mode === "line") {
    return "Line tool";
  }
  if (mode === "box") {
    return isOutlineVariant ? "Box outline tool" : "Box tool";
  }
  if (mode === "circle") {
    return isOutlineVariant ? "Circle outline tool" : "Circle tool";
  }
  return "Draw tool";
}

function getDrawModeFromButtonClick(buttonMode) {
  const baseButtonMode = getBaseDrawMode(buttonMode);
  if (
    OUTLINE_DRAW_MODE_BY_BASE.has(baseButtonMode) &&
    getBaseDrawMode(state.drawMode) === baseButtonMode
  ) {
    return isOutlineShapeDrawMode(state.drawMode)
      ? baseButtonMode
      : OUTLINE_DRAW_MODE_BY_BASE.get(baseButtonMode);
  }
  return buttonMode;
}

function updateDrawModeUI() {
  const isSprayMode = state.drawMode === "spray";
  if (drawModeButtons) {
    const buttons = Array.from(drawModeButtons.querySelectorAll(".draw-mode-button"));
    for (const button of buttons) {
      const buttonMode = getBaseDrawMode(button.dataset.drawMode || "");
      const isActive = buttonMode === getBaseDrawMode(state.drawMode);
      const isOutlineVariant = isActive && isOutlineShapeDrawMode(state.drawMode);
      const label = getDrawModeButtonLabel(buttonMode, isOutlineVariant);
      button.classList.toggle("is-active", isActive);
      button.classList.toggle("is-outline-mode", isOutlineVariant);
      button.setAttribute("aria-pressed", String(isActive));
      button.setAttribute("aria-label", label);
      button.title = label;
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
  if (state.exportMode) {
    updateExportResolutionLockButtonsUI();
  }
  updateGifPauseButtonUI();
}

function revokeExportBackgroundImageUrl() {
  if (state.exportBgImageObjectUrl) {
    URL.revokeObjectURL(state.exportBgImageObjectUrl);
  }
  exportBackgroundImageCache.clear();
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

function updateExportGuidelinesUI() {
  if (exportGuidelinesToggle) {
    exportGuidelinesToggle.checked = Boolean(state.exportGuidelinesEnabled);
  }
  if (exportOverlay) {
    exportOverlay.classList.toggle("has-guidelines", Boolean(state.exportGuidelinesEnabled));
  }
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
  updateExportGuidelinesUI();
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

  const sourceUrl =
    element.dataset.brushUrl ||
    element.dataset.gifPausedSrc ||
    element.currentSrc ||
    element.getAttribute("src") ||
    "";
  if (isGifUrl(sourceUrl)) {
    return true;
  }
  const brushId = Number(element.dataset.brushId);
  const brush = Number.isFinite(brushId) ? findBrushById(brushId) : null;
  const brushName = brush ? String(brush.name || "") : "";
  const fallbackUrl = sourceUrl || (brush ? String(brush.url || "") : "");

  return isGifUrl(fallbackUrl) || /\.gif$/i.test(brushName);
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
  if (nextTab === "edit" && (state.sceneRendererActive || state.sceneRendererPreparing)) {
    deactivateSceneRenderer();
  }
  if (nextTab !== "draw") {
    setBrushPickMode(false);
  }
  if (nextTab !== "draw" && nextTab !== "brushes") {
    cancelShapeDraft();
    clearCursorTrail();
  } else {
    state.pendingBrushGallerySelectionScroll = true;
  }
  updateSidebarTabUI();
  renderBrushGallery();
  updateEraseCursorVisibility();
  updateBrushCursorPreview();
  scheduleSessionSave();
  scheduleSceneRendererEvaluation();
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
  if (activeTab !== "edit") {
    viewport.classList.remove("is-edit-layer-clickable");
  }
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
  updateBrushImagePickerButton();
  if (activeTab === "community" && !state.savedCompositionsLoaded) {
    void loadSavedCompositions();
  }
  renderEditLayers();
}

function updateSidebarVisibilityUI() {
  controlsPanel.classList.toggle("is-collapsed", state.sidebarCollapsed);
  if (state.sidebarCollapsed && state.brushTagMenuOpen) {
    setBrushTagMenuOpen(false);
  }
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

function getViewportVisibilityBounds() {
  return {
    show: getViewportWorldBounds(STAMP_VIEWPORT_CULL_MARGIN_PX),
    hide: getViewportWorldBounds(STAMP_VIEWPORT_HIDE_MARGIN_PX)
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
    state.viewportRenderedStamps.add(stamp);
    if (isViewportCulledStamp(stamp)) {
      delete stamp.dataset.viewportCulled;
      stamp.classList.toggle("is-culled", isOcclusionCulledStamp(stamp));
      const source =
        stamp.dataset.sequenceDisplayedSource ||
        stamp.dataset.sequenceBaseSrc ||
        stamp.dataset.brushUrl ||
        stamp.dataset.gifPausedSrc ||
        "";
      if (
        !isOcclusionCulledStamp(stamp) &&
        !isSceneRendererStampSuppressed(stamp) &&
        source &&
        stamp.getAttribute("src") !== source
      ) {
        stamp.src = source;
        markGifPlaybackStart(stamp, source, true);
      }
      if (!isOcclusionCulledStamp(stamp) && !isSceneRendererStampSuppressed(stamp)) {
        applyGifPauseStateToImage(stamp);
      }
    }
    return;
  }

  if (state.gifAnimationsPaused || isViewportCulledStamp(stamp)) {
    return;
  }

  state.viewportRenderedStamps.delete(stamp);
  removeSequencePixelateProxy(stamp);
  stamp.dataset.viewportCulled = "true";
  stamp.classList.add("is-culled");
  stamp.src = TRANSPARENT_STAMP_SRC;
}

function normalizeViewportVisibilityBounds(viewportBounds) {
  if (viewportBounds && viewportBounds.show && viewportBounds.hide) {
    return viewportBounds;
  }
  return {
    show: viewportBounds || getViewportWorldBounds(STAMP_VIEWPORT_CULL_MARGIN_PX),
    hide: getViewportWorldBounds(STAMP_VIEWPORT_HIDE_MARGIN_PX)
  };
}

function updateStampViewportVisibility(stamp, viewportBounds = getViewportVisibilityBounds()) {
  if (!(stamp instanceof HTMLImageElement) || !stamp.classList.contains("stamp")) {
    return;
  }

  const bounds = getCachedStampWorldBounds(stamp);
  const visibilityBounds = normalizeViewportVisibilityBounds(viewportBounds);
  const targetBounds = isViewportCulledStamp(stamp) ? visibilityBounds.show : visibilityBounds.hide;
  setStampViewportRendered(stamp, rectsIntersect(bounds, targetBounds));
}

function refreshStampViewportVisibility() {
  const viewportBounds = getViewportVisibilityBounds();
  const showCandidates = getStampCandidatesInBounds(viewportBounds.show);
  for (const stamp of showCandidates) {
    if (
      stamp.parentElement === world &&
      !stamp.classList.contains("is-layer-hidden") &&
      rectsIntersect(getCachedStampWorldBounds(stamp), viewportBounds.show)
    ) {
      setStampViewportRendered(stamp, true);
    }
  }

  for (const stamp of Array.from(state.viewportRenderedStamps)) {
    if (
      stamp.parentElement !== world ||
      stamp.classList.contains("is-layer-hidden")
    ) {
      state.viewportRenderedStamps.delete(stamp);
      continue;
    }
    if (!rectsIntersect(getCachedStampWorldBounds(stamp), viewportBounds.hide)) {
      setStampViewportRendered(stamp, false);
    }
  }
  scheduleStampOcclusionRefresh();
}

function setStampOcclusionCulled(stamp, culled) {
  if (!(stamp instanceof HTMLImageElement)) {
    return false;
  }
  const stroke = getStampLayerStroke(stamp);
  const shouldCull =
    Boolean(culled) &&
    !shouldPauseGifImage(stamp) &&
    !strokeHasActiveSequenceTransform(stroke);
  if (shouldCull === isOcclusionCulledStamp(stamp)) {
    return false;
  }

  if (shouldCull) {
    state.occlusionCulledStamps.add(stamp);
    stamp.dataset.occlusionCulled = "true";
    removeSequencePixelateProxy(stamp);
    stamp.classList.add("is-culled");
    if (!isViewportCulledStamp(stamp)) {
      stamp.src = TRANSPARENT_STAMP_SRC;
    }
    return true;
  }

  state.occlusionCulledStamps.delete(stamp);
  delete stamp.dataset.occlusionCulled;
  if (isViewportCulledStamp(stamp)) {
    stamp.classList.add("is-culled");
    return true;
  }
  stamp.classList.remove("is-culled");
  const source =
    stamp.dataset.sequenceDisplayedSource ||
    stamp.dataset.sequenceBaseSrc ||
    stamp.dataset.brushUrl ||
    stamp.dataset.gifPausedSrc ||
    "";
  if (!isSceneRendererStampSuppressed(stamp) && source && stamp.getAttribute("src") !== source) {
    stamp.src = source;
    markGifPlaybackStart(stamp, source, true);
  }
  if (!isSceneRendererStampSuppressed(stamp)) {
    applyGifPauseStateToImage(stamp);
  }
  return true;
}

function cancelStampOcclusionRefresh() {
  if (state.stampOcclusionIdleId === null) {
    return;
  }
  if (typeof window.cancelIdleCallback === "function") {
    window.cancelIdleCallback(state.stampOcclusionIdleId);
  } else {
    window.clearTimeout(state.stampOcclusionIdleId);
  }
  state.stampOcclusionIdleId = null;
}

function invalidateStampOcclusion() {
  cancelStampOcclusionRefresh();
  const changed = [];
  for (const stamp of Array.from(state.occlusionCulledStamps)) {
    if (setStampOcclusionCulled(stamp, false)) {
      changed.push(stamp);
    }
  }
  if (changed.length) {
    syncSceneRendererElements(changed);
  }
}

function getStampOcclusionRecord(stamp) {
  const stroke = getStampLayerStroke(stamp);
  const source =
    stamp.dataset.sequenceDisplayedSource ||
    stamp.dataset.sequenceBaseSrc ||
    stamp.dataset.brushUrl ||
    "";
  const metadata = getStockBrushMetadataForSource(source);
  const rotation =
    (Number(stamp.dataset.rotation) || 0) +
    getStampLayerTransform(stroke, stamp).rotation;
  const normalizedQuarterTurn = Math.abs(rotation % 90);
  const axisAligned = normalizedQuarterTurn < 0.0001 || Math.abs(normalizedQuarterTurn - 90) < 0.0001;
  const hasSequence = stamp.dataset.sequenceActive === "1" || Boolean(
    stroke && isLayerSequenceEnabled(stroke)
  );
  const hasEffects = Boolean(
    stamp.style.filter ||
    stamp.classList.contains("has-sequence-pixelate-proxy") ||
    hasSequence
  );
  const opacity = clamp(Number(stamp.style.opacity) || 0, 0, 1);
  const blendMode = stroke ? getLayerBlendMode(stroke) : "normal";
  return {
    id: stamp,
    element: stamp,
    rect: getCachedStampWorldBounds(stamp),
    visible:
      stamp.parentElement === world &&
      !stamp.classList.contains("is-layer-hidden") &&
      !isViewportCulledStamp(stamp),
    cullable: !hasEffects,
    opaque: metadata?.opaque === true,
    opacity,
    blendMode,
    filter: stamp.style.filter || "",
    effects: hasEffects,
    axisAligned
  };
}

function refreshStampOcclusion() {
  state.stampOcclusionIdleId = null;
  if (
    !window.SceneOcclusion ||
    state.gifAnimationsPaused ||
    state.sequenceExportActive ||
    state.exportTask
  ) {
    invalidateStampOcclusion();
    return;
  }
  const viewportBounds = getViewportWorldBounds(0);
  const records = [];
  for (const child of world.children) {
    if (child instanceof HTMLImageElement && child.classList.contains("stamp")) {
      const record = getStampOcclusionRecord(child);
      if (record.visible) {
        records.push(record);
      }
    }
  }
  if (records.length < 2) {
    invalidateStampOcclusion();
    return;
  }

  const result = window.SceneOcclusion.compute(records, {
    viewport: viewportBounds,
    order: "bottom-to-top",
    tileSize: Math.max(4, 24 / Math.max(0.05, state.camera.scale)),
    idOf: (record) => record.id,
    rectOf: (record) => record.rect,
    isCullable: (record) => record.cullable === true,
    isOccluder: (record) =>
      record.opaque === true &&
      record.opacity === 1 &&
      record.blendMode === "normal" &&
      record.effects === false &&
      record.axisAligned === true
  });

  const nextOccluded = result.occludedIds;
  const changed = [];
  for (const stamp of Array.from(state.occlusionCulledStamps)) {
    if (!nextOccluded.has(stamp)) {
      if (setStampOcclusionCulled(stamp, false)) {
        changed.push(stamp);
      }
    }
  }
  for (const stamp of nextOccluded) {
    if (setStampOcclusionCulled(stamp, true)) {
      changed.push(stamp);
    }
  }
  if (changed.length) {
    syncSceneRendererElements(changed);
  }
}

function scheduleStampOcclusionRefresh() {
  if (state.stampOcclusionIdleId !== null || !window.SceneOcclusion) {
    return;
  }
  const run = () => refreshStampOcclusion();
  state.stampOcclusionIdleId = typeof window.requestIdleCallback === "function"
    ? window.requestIdleCallback(run, { timeout: 180 })
    : window.setTimeout(run, 32);
}

function createSceneRendererMessage(type, payload = {}) {
  return {
    protocol: SCENE_RENDER_PROTOCOL,
    version: SCENE_RENDER_VERSION,
    type,
    ...payload
  };
}

function getSceneStampId(stamp) {
  if (!(stamp instanceof HTMLImageElement)) {
    return null;
  }
  if (!sceneStampIdMap.has(stamp)) {
    sceneStampIdMap.set(stamp, `stamp-${nextSceneStampId++}`);
  }
  return sceneStampIdMap.get(stamp);
}

function getSceneRendererStampSource(stamp) {
  return (
    stamp?.dataset?.sequenceDisplayedSource ||
    stamp?.dataset?.sequenceImageCycleSrc ||
    stamp?.dataset?.sequenceBaseSrc ||
    stamp?.dataset?.brushUrl ||
    stamp?.dataset?.gifPausedSrc ||
    ""
  );
}

function getSceneRendererMimeType(source) {
  const dataMatch = String(source || "").match(/^data:([^;,]+)/i);
  if (dataMatch) {
    return dataMatch[1].toLowerCase();
  }
  const cleanSource = String(source || "").split(/[?#]/)[0].toLowerCase();
  if (cleanSource.endsWith(".gif")) return "image/gif";
  if (cleanSource.endsWith(".png")) return "image/png";
  if (cleanSource.endsWith(".webp")) return "image/webp";
  if (cleanSource.endsWith(".jpg") || cleanSource.endsWith(".jpeg")) return "image/jpeg";
  return "";
}

function getSceneRendererBlurAmount(stamp) {
  const filter = String(stamp?.style?.filter || "").trim();
  if (!filter) {
    return 0;
  }
  const match = filter.match(/^blur\(\s*([0-9]+(?:\.[0-9]+)?)px\s*\)$/i);
  return match ? clamp(Number(match[1]) || 0, 0, 256) : null;
}

function getSceneRendererTransform(stamp) {
  const left = parseFloat(stamp.style.left) || 0;
  const top = parseFloat(stamp.style.top) || 0;
  const baseWidth = Math.max(1, parseFloat(stamp.style.width) || 1);
  const baseHeight = Math.max(1, parseFloat(stamp.style.height) || 1);
  const transform = stamp.style.transform || "none";
  try {
    const matrix = new DOMMatrix(transform);
    const scaleX = Math.max(0.0001, Math.hypot(matrix.a, matrix.b));
    const scaleY = Math.max(0.0001, Math.hypot(matrix.c, matrix.d));
    return {
      centerX: left + baseWidth / 2 + matrix.e,
      centerY: top + baseHeight / 2 + matrix.f,
      width: baseWidth * scaleX,
      height: baseHeight * scaleY,
      rotation: (Math.atan2(matrix.b, matrix.a) * 180) / Math.PI
    };
  } catch (error) {
    return {
      centerX: left + baseWidth / 2,
      centerY: top + baseHeight / 2,
      width: baseWidth,
      height: baseHeight,
      rotation: Number(stamp.dataset.rotation) || 0
    };
  }
}

function getSceneRendererStampRecord(stamp) {
  if (!(stamp instanceof HTMLImageElement) || stamp.parentElement !== world) {
    return null;
  }
  const sourceUrl = getSceneRendererStampSource(stamp);
  if (
    !sourceUrl ||
    sourceUrl === TRANSPARENT_STAMP_SRC ||
    sceneRendererUnsupportedSources.has(sourceUrl)
  ) {
    return null;
  }
  const blurAmount = getSceneRendererBlurAmount(stamp);
  if (blurAmount === null || stamp.classList.contains("has-sequence-pixelate-proxy")) {
    return null;
  }
  const sourceMetadata = getStockBrushMetadataForSource(sourceUrl);
  const brushId = Number(stamp.dataset.brushId);
  const brush = Number.isFinite(brushId) ? findBrushById(brushId) : null;
  const gifSource = isGifUrl(sourceUrl) || Boolean(brush && getBrushSourceIsGif(brush));
  const metadataAnimated = sourceMetadata?.animated === true;
  const sourceMimeType = getSceneRendererMimeType(sourceUrl);
  const potentiallyAnimatedUnknownSource = Boolean(
    !sourceMetadata &&
    !gifSource &&
    (
      /^(?:image\/(?:png|webp|avif|svg\+xml))$/i.test(sourceMimeType) ||
      /^(?:blob:)/i.test(sourceUrl) ||
      /\.(?:png|webp|avif|svg)(?:[?#]|$)/i.test(sourceUrl)
    )
  );
  if (potentiallyAnimatedUnknownSource) {
    return null;
  }
  if (metadataAnimated && !gifSource) {
    return null;
  }
  const sourceTypeKnown = gifSource || Boolean(
    sourceMimeType ||
    brush ||
    sourceMetadata
  );
  const animated = gifSource ? true : sourceTypeKnown ? false : null;
  const stroke = getStampLayerStroke(stamp);
  if (stroke && getLayerBlendMode(stroke) !== "normal") {
    // CSS mix-blend-mode sees the live canvas backdrop, while the worker canvas
    // is composited as one surface. Keep the DOM renderer for exact parity.
    return null;
  }
  if (stroke?.animationPaused) {
    return null;
  }
  const geometry = getSceneRendererTransform(stamp);
  let startedAt = Number(stamp.dataset.gifPlaybackStartedAt);
  if (!Number.isFinite(startedAt)) {
    startedAt = performance.now();
    if (gifSource) {
      stamp.dataset.gifPlaybackSource = sourceUrl;
      stamp.dataset.gifPlaybackStartedAt = String(startedAt);
    }
  }
  return {
    id: getSceneStampId(stamp),
    sourceUrl,
    sourceType: gifSource ? "gif" : sourceTypeKnown ? "static" : "auto",
    ...(typeof animated === "boolean" ? { animated } : {}),
    mimeType: sourceMimeType,
    centerX: geometry.centerX,
    centerY: geometry.centerY,
    width: geometry.width,
    height: geometry.height,
    rotation: geometry.rotation,
    opacity: clamp(Number(stamp.style.opacity) || 0, 0, 1),
    blendMode: stroke ? getLayerBlendMode(stroke) : "normal",
    imageRendering: stamp.style.imageRendering === "auto" ? "auto" : "pixelated",
    visible:
      !stamp.classList.contains("is-layer-hidden") &&
      !isOcclusionCulledStamp(stamp),
    blurAmount,
    startedAt,
    phaseOffsetMs: 0,
    animationPaused: false,
    animationPausedAt: 0
  };
}

function getSceneRendererStampsInOrder() {
  return Array.from(world.children).filter(
    (element) => element instanceof HTMLImageElement && element.classList.contains("stamp")
  );
}

function collectSceneRendererRecords() {
  const records = [];
  for (const stamp of getSceneRendererStampsInOrder()) {
    if (stamp.classList.contains("is-layer-hidden")) {
      continue;
    }
    const record = getSceneRendererStampRecord(stamp);
    if (!record) {
      return null;
    }
    records.push(record);
  }
  return records;
}

function hasSceneRendererCapability() {
  return Boolean(
    sceneRenderCanvas &&
    typeof Worker === "function" &&
    typeof sceneRenderCanvas.transferControlToOffscreen === "function" &&
    typeof window.OffscreenCanvas === "function" &&
    typeof window.createImageBitmap === "function"
  );
}

function canUseSceneRendererMode() {
  return Boolean(
    !state.sceneRendererDisabled &&
    hasSceneRendererCapability() &&
    !state.exportMode &&
    !state.exportTask &&
    state.sidebarTab !== "edit" &&
    !state.eraseMode &&
    !state.brushPickMode &&
    !state.gifAnimationsPaused &&
    !hasActiveSequenceEffectOnCanvas() &&
    !state.brushCropEditor.open &&
    document.visibilityState !== "hidden"
  );
}

function canStartSceneRendererMode() {
  return Boolean(
    canUseSceneRendererMode() &&
    !state.drawing &&
    !state.placementTask &&
    !state.shapeDraft &&
    !state.panning &&
    !state.touchGesture &&
    performance.now() - state.sceneRendererLastCameraChangeAt >= 160
  );
}

function sceneRendererMeetsLoadThreshold() {
  const lowCoreDevice = Number(navigator.hardwareConcurrency) > 0 && navigator.hardwareConcurrency <= 4;
  const animatedThreshold = lowCoreDevice
    ? Math.max(400, Math.round(SCENE_RENDER_MIN_ANIMATED_STAMPS * 0.75))
    : SCENE_RENDER_MIN_ANIMATED_STAMPS;
  const totalThreshold = lowCoreDevice
    ? Math.max(1000, Math.round(SCENE_RENDER_MIN_TOTAL_STAMPS * 0.75))
    : SCENE_RENDER_MIN_TOTAL_STAMPS;
  let total = 0;
  let animated = 0;
  const stamps = world.getElementsByClassName("stamp");
  for (let index = 0; index < stamps.length; index += 1) {
    const stamp = stamps[index];
    if (!(stamp instanceof HTMLImageElement)) {
      continue;
    }
    if (stamp.classList.contains("is-layer-hidden")) {
      continue;
    }
    total += 1;
    const source = getSceneRendererStampSource(stamp);
    const metadata = getStockBrushMetadataForSource(source);
    let animatedSource = isGifUrl(source) || metadata?.animated === true;
    if (!animatedSource) {
      const brushId = Number(stamp.dataset.brushId);
      const brush = Number.isFinite(brushId) ? findBrushById(brushId) : null;
      animatedSource = Boolean(brush && getBrushSourceIsGif(brush));
    }
    if (animatedSource) {
      animated += 1;
    }
    if (animated >= animatedThreshold || total >= totalThreshold) {
      return true;
    }
  }
  return false;
}

function getSceneRendererCanvasMetrics() {
  const rect = viewport.getBoundingClientRect();
  const visibleCount = Math.max(1, state.viewportRenderedStamps.size);
  const dprCap = visibleCount >= 8000 ? 1 : visibleCount >= 3000 ? 1.25 : 1.5;
  return {
    width: Math.max(1, rect.width),
    height: Math.max(1, rect.height),
    dpr: Math.max(1, Math.min(Number(window.devicePixelRatio) || 1, dprCap))
  };
}

function getSceneRendererMemoryBudgetBytes() {
  const deviceMemory = Number(navigator.deviceMemory);
  if (Number.isFinite(deviceMemory) && deviceMemory <= 4) {
    return 96 * 1024 * 1024;
  }
  if (Number.isFinite(deviceMemory) && deviceMemory <= 8) {
    return 192 * 1024 * 1024;
  }
  return 256 * 1024 * 1024;
}

function postSceneRendererMessage(type, payload = {}, transfer = []) {
  if (!sceneRendererWorker) {
    return false;
  }
  try {
    sceneRendererWorker.postMessage(createSceneRendererMessage(type, payload), transfer);
    return true;
  } catch (error) {
    failSceneRenderer(error);
    return false;
  }
}

function settleSceneRendererSceneRequest(revision, error = null, value = null) {
  const request = sceneRendererSceneRequests.get(Number(revision));
  if (!request) {
    return;
  }
  sceneRendererSceneRequests.delete(Number(revision));
  window.clearTimeout(request.timeoutId);
  if (error) {
    request.reject(error);
  } else {
    request.resolve(value);
  }
}

function handleSceneRendererMessage(event) {
  const message = event.data || {};
  if (message.protocol !== SCENE_RENDER_PROTOCOL || message.version !== SCENE_RENDER_VERSION) {
    return;
  }

  if (message.type === "initialized") {
    sceneRendererInitialized = true;
    sceneRendererInitResolve?.(message);
    sceneRendererInitResolve = null;
    sceneRendererInitReject = null;
    return;
  }

  if (message.type === "source-status") {
    const sourceUrl = String(message.sourceUrl || "");
    if (message.status === "ready" && sourceUrl) {
      sceneRendererReadySources.add(sourceUrl);
      if (state.sceneRendererActive) {
        suppressSceneRendererStampsForSource(sourceUrl);
      }
    } else if (message.status === "loading" && sourceUrl) {
      // A source can be reloaded after worker-side eviction. Do not allow a
      // stale ready marker to hide its DOM fallback before a frame presents.
      sceneRendererReadySources.delete(sourceUrl);
    } else if (message.status === "evicted" && sourceUrl) {
      sceneRendererReadySources.delete(sourceUrl);
      if (
        state.sceneRendererActive &&
        getSceneRendererStampsInOrder().some(
          (stamp) => getSceneRendererStampSource(stamp) === sourceUrl
        )
      ) {
        deactivateSceneRenderer();
      }
    } else if (
      message.status === "error" &&
      (state.sceneRendererActive || state.sceneRendererPreparing) &&
      getSceneRendererStampsInOrder().some(
        (stamp) => getSceneRendererStampSource(stamp) === sourceUrl
      )
    ) {
      const error = new Error(message.error?.message || "A scene source could not be decoded.");
      error.name = "SceneRendererFallbackError";
      sceneRendererUnsupportedSources.add(sourceUrl);
      deactivateSceneRenderer({ dispose: true, reason: error });
    }
    return;
  }

  if (
    (message.type === "ack" && message.action === "upsert") ||
    message.type === "frame-presented"
  ) {
    const requestId = String(message.requestId || "");
    if (message.ignored) {
      clearSceneRendererUpsertRequest(requestId);
      return;
    }
    if (message.type === "ack" && message.presented !== true && !message.ignored) {
      return;
    }
    const presentedRevision = Number(message.revision);
    if (!Number.isFinite(presentedRevision)) {
      return;
    }
    for (const [pendingRequestId, request] of sceneRendererUpsertRequests) {
      if (request.revision > presentedRevision) {
        continue;
      }
      sceneRendererUpsertRequests.delete(pendingRequestId);
      for (const item of request.stamps) {
        const { stamp, recordId } = item;
        if (sceneRendererPendingStampRevision.get(stamp) !== request.revision) {
          continue;
        }
        sceneRendererPendingStampRevision.delete(stamp);
        if (
          state.sceneRendererActive &&
          stamp.parentElement === world &&
          getSceneStampId(stamp) === recordId &&
          !state.sceneRendererPendingElements.has(stamp)
        ) {
          suppressSceneRendererStamp(stamp);
        }
      }
    }
    return;
  }

  if (message.type === "scene-ready") {
    settleSceneRendererSceneRequest(message.revision, null, message);
    return;
  }

  if (message.type === "scene-error") {
    const firstError = Array.isArray(message.errors) ? message.errors[0]?.error : null;
    const error = new Error(firstError?.message || "The accelerated scene could not be prepared.");
    const failedSourceUrl = String(
      Array.isArray(message.errors) ? message.errors[0]?.sourceUrl || "" : ""
    );
    if (failedSourceUrl) {
      sceneRendererUnsupportedSources.add(failedSourceUrl);
      error.name = "SceneRendererFallbackError";
    }
    if (sceneRendererSceneRequests.has(Number(message.revision))) {
      settleSceneRendererSceneRequest(message.revision, error);
    } else if (
      Number(message.revision) === state.sceneRenderRevision &&
      (state.sceneRendererActive || state.sceneRendererPreparing)
    ) {
      failSceneRenderer(error);
    }
    if (
      failedSourceUrl &&
      (state.sceneRendererActive || state.sceneRendererPreparing)
    ) {
      deactivateSceneRenderer({ dispose: true, reason: error });
    }
    return;
  }

  if (message.type === "error") {
    const error = new Error(message.error?.message || "The accelerated renderer failed.");
    if (!sceneRendererInitialized && sceneRendererInitReject) {
      sceneRendererInitReject(error);
      sceneRendererInitResolve = null;
      sceneRendererInitReject = null;
    } else if (state.sceneRendererActive || state.sceneRendererPreparing) {
      failSceneRenderer(error);
    }
  }
}

function clearSceneRendererUpsertRequest(requestId) {
  const request = sceneRendererUpsertRequests.get(String(requestId || ""));
  if (!request) {
    return;
  }
  sceneRendererUpsertRequests.delete(String(requestId || ""));
  for (const { stamp } of request.stamps) {
    if (sceneRendererPendingStampRevision.get(stamp) === request.revision) {
      sceneRendererPendingStampRevision.delete(stamp);
    }
  }
}

function clearSceneRendererUpsertRequests() {
  for (const requestId of Array.from(sceneRendererUpsertRequests.keys())) {
    clearSceneRendererUpsertRequest(requestId);
  }
}

function resetSceneRendererWorkerState(reason = null) {
  sceneRendererInitialized = false;
  sceneRendererInitPromise = null;
  sceneRendererInitResolve = null;
  sceneRendererInitReject = null;
  sceneRendererReadySources.clear();
  clearSceneRendererUpsertRequests();
  const stopError = reason || new Error("The accelerated renderer stopped.");
  for (const request of sceneRendererSceneRequests.values()) {
    window.clearTimeout(request.timeoutId);
    request.reject(stopError);
  }
  sceneRendererSceneRequests.clear();
}

function replaceTransferredSceneRenderCanvas() {
  if (!sceneRenderCanvas?.parentElement) {
    return;
  }
  const replacement = document.createElement("canvas");
  replacement.id = "sceneRenderCanvas";
  replacement.hidden = true;
  replacement.setAttribute("aria-hidden", "true");
  sceneRenderCanvas.replaceWith(replacement);
  sceneRenderCanvas = replacement;
}

async function initializeSceneRendererWorker() {
  if (sceneRendererInitialized && sceneRendererWorker) {
    return true;
  }
  if (sceneRendererInitPromise) {
    return sceneRendererInitPromise;
  }
  if (!hasSceneRendererCapability()) {
    return false;
  }

  sceneRendererInitPromise = new Promise((resolve, reject) => {
    sceneRendererInitResolve = resolve;
    sceneRendererInitReject = reject;
  })
    .then(() => true)
    .catch(() => false);

  try {
    sceneRendererWorker = new Worker(SCENE_RENDER_WORKER_URL, { type: "module" });
    sceneRendererWorker.addEventListener("message", handleSceneRendererMessage);
    sceneRendererWorker.addEventListener("error", (event) => {
      const error = new Error(event.message || "The accelerated renderer worker crashed.");
      if (!sceneRendererInitialized && sceneRendererInitReject) {
        sceneRendererInitReject(error);
      } else {
        failSceneRenderer(error);
      }
    });
    const offscreenCanvas = sceneRenderCanvas.transferControlToOffscreen();
    const metrics = getSceneRendererCanvasMetrics();
    sceneRendererWorker.postMessage(
      createSceneRendererMessage("init", {
        requestId: "scene-render-init",
        canvas: offscreenCanvas,
        width: metrics.width,
        height: metrics.height,
        dpr: metrics.dpr,
        timeOrigin: performance.timeOrigin,
        camera: { ...state.camera },
        options: {
          memoryBudgetBytes: getSceneRendererMemoryBudgetBytes(),
          decodeConcurrency: 2
        }
      }),
      [offscreenCanvas]
    );
    window.setTimeout(() => {
      if (!sceneRendererInitialized && sceneRendererInitReject) {
        sceneRendererInitReject(new Error("The accelerated renderer did not initialize in time."));
        sceneRendererInitResolve = null;
        sceneRendererInitReject = null;
      }
    }, 5000);
  } catch (error) {
    sceneRendererInitReject?.(error);
    sceneRendererInitResolve = null;
    sceneRendererInitReject = null;
  }

  const initialized = await sceneRendererInitPromise;
  if (!initialized) {
    state.sceneRendererDisabled = true;
    sceneRendererWorker?.terminate();
    sceneRendererWorker = null;
    resetSceneRendererWorkerState();
    replaceTransferredSceneRenderCanvas();
  }
  return initialized;
}

function isSceneRendererStampSuppressed(stamp) {
  return stamp instanceof HTMLImageElement && stamp.dataset.sceneRendererSuppressed === "true";
}

function suppressSceneRendererStamp(stamp) {
  if (!(stamp instanceof HTMLImageElement) || stamp.parentElement !== world) {
    return;
  }
  stamp.dataset.sceneRendererSuppressed = "true";
  stamp.classList.add("is-scene-rendered");
  if (stamp.getAttribute("src") !== TRANSPARENT_STAMP_SRC) {
    stamp.src = TRANSPARENT_STAMP_SRC;
  }
}

function restoreSceneRendererStamp(stamp) {
  if (!(stamp instanceof HTMLImageElement) || !isSceneRendererStampSuppressed(stamp)) {
    return;
  }
  delete stamp.dataset.sceneRendererSuppressed;
  stamp.classList.remove("is-scene-rendered");
  if (isRenderCulledStamp(stamp)) {
    stamp.src = TRANSPARENT_STAMP_SRC;
    return;
  }
  const source = getSceneRendererStampSource(stamp);
  if (source && stamp.getAttribute("src") !== source) {
    stamp.src = source;
    markGifPlaybackStart(stamp, source, true);
  }
  applyGifPauseStateToImage(stamp);
}

function suppressSceneRendererStampsForSource(sourceUrl) {
  for (const stamp of getSceneRendererStampsInOrder()) {
    if (
      getSceneRendererStampSource(stamp) === sourceUrl &&
      !sceneRendererPendingStampRevision.has(stamp) &&
      !state.sceneRendererPendingElements.has(stamp)
    ) {
      suppressSceneRendererStamp(stamp);
    }
  }
}

function failSceneRenderer(error) {
  if (state.sceneRendererDisabled && !sceneRendererWorker) {
    return;
  }
  console.warn("Accelerated scene renderer fell back to DOM.", error);
  state.sceneRendererDisabled = true;
  deactivateSceneRenderer({ dispose: true });
}

function deactivateSceneRenderer(options = {}) {
  const dispose = options.dispose === true;
  state.sceneRendererActive = false;
  state.sceneRendererPreparing = false;
  viewport.classList.remove("is-accelerated-scene");
  if (state.sceneRendererSyncRafId !== null) {
    window.cancelAnimationFrame(state.sceneRendererSyncRafId);
    state.sceneRendererSyncRafId = null;
  }
  if (state.sceneRendererElementSyncRafId !== null) {
    window.cancelAnimationFrame(state.sceneRendererElementSyncRafId);
    state.sceneRendererElementSyncRafId = null;
  }
  state.sceneRendererPendingElements.clear();
  clearSceneRendererUpsertRequests();
  if (sceneRenderCanvas) {
    sceneRenderCanvas.hidden = true;
  }
  for (const stamp of getSceneRendererStampsInOrder()) {
    restoreSceneRendererStamp(stamp);
  }

  if (dispose) {
    sceneRendererWorker?.terminate();
    sceneRendererWorker = null;
    resetSceneRendererWorkerState(options.reason || null);
    replaceTransferredSceneRenderCanvas();
  } else if (sceneRendererWorker && sceneRendererInitialized) {
    postSceneRendererMessage("pause", { paused: true, now: performance.now() });
  }
}

function supersedeSceneRendererSceneRequests(revision) {
  for (const [pendingRevision, pending] of sceneRendererSceneRequests) {
    if (pendingRevision < revision) {
      window.clearTimeout(pending.timeoutId);
      sceneRendererSceneRequests.delete(pendingRevision);
      pending.resolve({ stale: true, revision: pendingRevision });
    }
  }
}

function requestSceneRendererScene(records, revision) {
  supersedeSceneRendererSceneRequests(revision);
  return new Promise((resolve, reject) => {
    const timeoutId = window.setTimeout(() => {
      sceneRendererSceneRequests.delete(revision);
      reject(new Error("The accelerated scene took too long to prepare."));
    }, SCENE_RENDER_PREPARE_TIMEOUT_MS);
    sceneRendererSceneRequests.set(revision, { resolve, reject, timeoutId });
    if (!postSceneRendererMessage("scene", { revision, records })) {
      settleSceneRendererSceneRequest(
        revision,
        new Error("The accelerated scene could not be sent to its worker.")
      );
    }
  });
}

async function activateSceneRenderer() {
  if (
    state.sceneRendererActive ||
    state.sceneRendererPreparing ||
    !canStartSceneRendererMode() ||
    !sceneRendererMeetsLoadThreshold()
  ) {
    return;
  }
  let records = collectSceneRendererRecords();
  if (!records?.length) {
    return;
  }
  state.sceneRendererPreparing = true;
  try {
    if (!await initializeSceneRendererWorker()) {
      return;
    }
    postSceneRendererMessage("pause", { paused: false, now: performance.now() });

    for (let attempt = 0; attempt < 3; attempt += 1) {
      if (!canStartSceneRendererMode()) {
        return;
      }
      resizeSceneRenderer();
      syncSceneRendererCamera();
      const mutationRevision = state.sceneMutationRevision;
      const revision = ++state.sceneRenderRevision;
      const expectedStampCount = records.length;
      const prepared = await requestSceneRendererScene(records, revision);
      if (prepared?.stale) {
        records = collectSceneRendererRecords();
        if (!records) {
          return;
        }
        continue;
      }
      const currentRecords = collectSceneRendererRecords();
      if (!currentRecords || !canStartSceneRendererMode()) {
        return;
      }
      if (
        currentRecords.length !== expectedStampCount ||
        state.sceneMutationRevision !== mutationRevision
      ) {
        records = currentRecords;
        continue;
      }

      for (const record of records) {
        sceneRendererReadySources.add(record.sourceUrl);
      }
      state.sceneRendererActive = true;
      state.sceneRendererPreparing = false;
      viewport.classList.add("is-accelerated-scene");
      sceneRenderCanvas.hidden = false;
      postSceneRendererMessage("pause", { paused: false, now: performance.now() });
      for (const stamp of getSceneRendererStampsInOrder()) {
        suppressSceneRendererStamp(stamp);
      }
      return;
    }
  } catch (error) {
    if (error?.name !== "SceneRendererFallbackError") {
      failSceneRenderer(error);
    }
  } finally {
    state.sceneRendererPreparing = false;
    if (!state.sceneRendererActive && sceneRendererInitialized) {
      postSceneRendererMessage("pause", { paused: true, now: performance.now() });
    }
    if (
      !state.sceneRendererActive &&
      canStartSceneRendererMode() &&
      sceneRendererMeetsLoadThreshold() &&
      collectSceneRendererRecords()
    ) {
      window.setTimeout(scheduleSceneRendererEvaluation, 80);
    }
  }
}

function scheduleSceneRendererEvaluation() {
  if (state.sceneRendererSyncRafId !== null) {
    return;
  }
  state.sceneRendererSyncRafId = window.requestAnimationFrame(() => {
    state.sceneRendererSyncRafId = null;
    if (state.sceneRendererActive) {
      if (
        !canUseSceneRendererMode() ||
        !sceneRendererMeetsLoadThreshold() ||
        !collectSceneRendererRecords()
      ) {
        deactivateSceneRenderer();
      }
      return;
    }
    if (canStartSceneRendererMode() && sceneRendererMeetsLoadThreshold()) {
      void activateSceneRenderer();
    }
  });
}

function scheduleSceneRendererFullSync() {
  if (!state.sceneRendererActive) {
    scheduleSceneRendererEvaluation();
    return;
  }
  if (state.sceneRendererSyncRafId !== null) {
    return;
  }
  state.sceneRendererSyncRafId = window.requestAnimationFrame(() => {
    state.sceneRendererSyncRafId = null;
    const records = collectSceneRendererRecords();
    if (!records || !canUseSceneRendererMode()) {
      deactivateSceneRenderer();
      return;
    }
    const revision = ++state.sceneRenderRevision;
    if (records.some((record) => !sceneRendererReadySources.has(record.sourceUrl))) {
      deactivateSceneRenderer();
      scheduleSceneRendererEvaluation();
      return;
    }
    void requestSceneRendererScene(records, revision)
      .then((prepared) => {
        if (!state.sceneRendererActive || prepared?.stale) {
          return;
        }
        for (const record of records) {
          sceneRendererReadySources.add(record.sourceUrl);
        }
        for (const stamp of getSceneRendererStampsInOrder()) {
          suppressSceneRendererStamp(stamp);
        }
      })
      .catch(failSceneRenderer);
  });
}

function noteSceneRendererMutation() {
  state.sceneMutationRevision += 1;
}

function syncSceneRendererElements(elements) {
  const elementList = Array.from(elements || []);
  for (const element of elementList) {
    state.sceneRendererPendingElements.delete(element);
  }
  noteSceneRendererMutation();
  if ((state.sceneRendererActive || state.sceneRendererPreparing) && !canUseSceneRendererMode()) {
    deactivateSceneRenderer();
    return;
  }
  if (state.sceneRendererPreparing) {
    return;
  }
  if (!state.sceneRendererActive) {
    scheduleSceneRendererEvaluation();
    return;
  }
  const stamps = elementList.filter(
    (element) => element instanceof HTMLImageElement && element.parentElement === world
  );
  const records = [];
  const stampsAwaitingPresentation = [];
  for (const stamp of stamps) {
    const record = getSceneRendererStampRecord(stamp);
    if (!record) {
      deactivateSceneRenderer();
      return;
    }
    records.push(record);
    if (!sceneRendererReadySources.has(record.sourceUrl)) {
      deactivateSceneRenderer();
      scheduleSceneRendererEvaluation();
      return;
    }
    if (isSceneRendererStampSuppressed(stamp)) {
      suppressSceneRendererStamp(stamp);
    } else {
      stampsAwaitingPresentation.push({ stamp, recordId: record.id });
    }
  }
  if (!records.length) {
    return;
  }
  const revision = ++state.sceneRenderRevision;
  supersedeSceneRendererSceneRequests(revision);
  const requestId = `scene-render-upsert-${revision}`;
  if (stampsAwaitingPresentation.length) {
    for (const { stamp } of stampsAwaitingPresentation) {
      sceneRendererPendingStampRevision.set(stamp, revision);
    }
    sceneRendererUpsertRequests.set(requestId, {
      revision,
      stamps: stampsAwaitingPresentation
    });
  }
  if (!postSceneRendererMessage("upsert", {
    requestId,
    revision,
    records
  })) {
    clearSceneRendererUpsertRequest(requestId);
  }
}

function scheduleSceneRendererElementsSync(elements) {
  const elementList = Array.from(elements || []);
  if (!state.sceneRendererActive) {
    syncSceneRendererElements(elementList);
    return;
  }
  for (const element of elementList) {
    if (element instanceof HTMLImageElement) {
      state.sceneRendererPendingElements.add(element);
    }
  }
  if (state.sceneRendererElementSyncRafId !== null) {
    return;
  }
  state.sceneRendererElementSyncRafId = window.requestAnimationFrame(() => {
    state.sceneRendererElementSyncRafId = null;
    if (!state.sceneRendererPendingElements.size) {
      return;
    }
    const pendingElements = Array.from(state.sceneRendererPendingElements);
    state.sceneRendererPendingElements.clear();
    syncSceneRendererElements(pendingElements);
  });
}

function removeSceneRendererElements(elements) {
  const ids = Array.from(elements || [])
    .map((element) => sceneStampIdMap.get(element))
    .filter(Boolean);
  noteSceneRendererMutation();
  if (!state.sceneRendererActive || !ids.length) {
    return;
  }
  const revision = ++state.sceneRenderRevision;
  supersedeSceneRendererSceneRequests(revision);
  postSceneRendererMessage("remove", {
    revision,
    ids
  });
}

function syncSceneRendererOrder() {
  noteSceneRendererMutation();
  if (!state.sceneRendererActive) {
    scheduleSceneRendererEvaluation();
    return;
  }
  const ids = getSceneRendererStampsInOrder().map(getSceneStampId);
  const revision = ++state.sceneRenderRevision;
  supersedeSceneRendererSceneRequests(revision);
  postSceneRendererMessage("order", {
    revision,
    ids
  });
}

function syncSceneRendererCamera() {
  if ((!state.sceneRendererActive && !state.sceneRendererPreparing) || !sceneRendererInitialized) {
    return;
  }
  postSceneRendererMessage("camera", { camera: { ...state.camera } });
}

function resizeSceneRenderer() {
  if (!sceneRendererInitialized) {
    return;
  }
  const metrics = getSceneRendererCanvasMetrics();
  postSceneRendererMessage("resize", metrics);
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
    setStampOcclusionCulled(stamps[index], false);
    setStampViewportRendered(stamps[index], true);
  }
  state.occlusionCulledStamps.clear();
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
  const stroke = getStampLayerStroke(element);
  const layerTransform = getStampLayerTransform(stroke, element);
  const rotation = (Number(element.dataset.rotation) || 0) + layerTransform.rotation;
  const visualWidth = width * layerTransform.scale;
  const visualHeight = height * layerTransform.scale;
  const centerX = left + width / 2 + layerTransform.x;
  const centerY = top + height / 2 + layerTransform.y;
  return getStampWorldBoundsFromLayout(
    centerX - visualWidth / 2,
    centerY - visualHeight / 2,
    visualWidth,
    visualHeight,
    rotation
  );
}

function getStampSequenceVisualWorldBounds(stroke, element, visual) {
  if (!(element instanceof HTMLImageElement) || !visual) {
    return getCachedStampWorldBounds(element);
  }
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  const layerTransform = visual.groupedTransform
    ? getStampGroupedLayerTransform(stroke, element, visual.groupedTransform)
    : getStampLayerTransform(stroke, element);
  const scale = Math.max(
    0.001,
    Math.abs(layerTransform.scale * (Number(visual.scale) || 1))
  );
  const rotation =
    (Number(element.dataset.rotation) || 0) +
    layerTransform.rotation +
    (Number(visual.rotationOffset) || 0);
  const centerX =
    left + width / 2 + layerTransform.x + (Number(visual.moveX) || 0);
  const centerY =
    top + height / 2 + layerTransform.y + (Number(visual.moveY) || 0);
  const visualWidth = width * scale;
  const visualHeight = height * scale;
  return getStampWorldBoundsFromLayout(
    centerX - visualWidth / 2,
    centerY - visualHeight / 2,
    visualWidth,
    visualHeight,
    rotation
  );
}

function getStampIndexCellCoord(value) {
  return Math.floor(value / STAMP_INDEX_CELL_SIZE);
}

function getStampIndexCellKey(cellX, cellY) {
  return `${cellX}:${cellY}`;
}

function getStampCandidatesInBounds(bounds) {
  const candidates = new Set();
  if (!bounds) {
    return candidates;
  }

  const minCellX = getStampIndexCellCoord(bounds.left);
  const maxCellX = getStampIndexCellCoord(bounds.right);
  const minCellY = getStampIndexCellCoord(bounds.top);
  const maxCellY = getStampIndexCellCoord(bounds.bottom);
  const cellColumns = Math.max(0, maxCellX - minCellX + 1);
  const cellRows = Math.max(0, maxCellY - minCellY + 1);
  const cellCount = cellColumns * cellRows;
  const fullScanThreshold = Math.max(256, state.stampCount * 3);

  if (!state.stampSpatialBuckets.size || cellCount > fullScanThreshold) {
    for (const stamp of getVisibleStampElements()) {
      candidates.add(stamp);
    }
    return candidates;
  }

  for (let cellX = minCellX; cellX <= maxCellX; cellX += 1) {
    for (let cellY = minCellY; cellY <= maxCellY; cellY += 1) {
      const bucket = state.stampSpatialBuckets.get(getStampIndexCellKey(cellX, cellY));
      if (!bucket) {
        continue;
      }
      for (const stamp of bucket) {
        candidates.add(stamp);
      }
    }
  }
  return candidates;
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

  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  if (width <= 0 || height <= 0) {
    return null;
  }
  const bounds = getStampWorldBounds(element);
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
  if (state.exportResolutionLocked === false && state.exportCustomResolution) {
    const custom = normalizeExportCustomResolution(state.exportCustomResolution);
    if (custom) {
      return custom;
    }
  }
  const multiplier = getExportScaleMultiplier(normalized);
  const width = Math.max(1, Math.round((normalized.right - normalized.left) * multiplier));
  const height = Math.max(1, Math.round((normalized.bottom - normalized.top) * multiplier));
  return { width, height };
}

function getExportScaledResolutionForScale(bounds, scalePercent) {
  const normalized = normalizeExportSelectionBounds(bounds);
  const rawMultiplier = Number(scalePercent) / 100;
  const multiplier = clamp(
    Number.isFinite(rawMultiplier) ? rawMultiplier : 1,
    getExportMinScaleMultiplier(normalized),
    getExportMaxScaleMultiplier(normalized)
  );
  return {
    width: Math.max(1, Math.round((normalized.right - normalized.left) * multiplier)),
    height: Math.max(1, Math.round((normalized.bottom - normalized.top) * multiplier))
  };
}

function normalizeExportCustomResolution(resolution) {
  if (!resolution || typeof resolution !== "object") {
    return null;
  }
  const width = Math.round(Number(resolution.width));
  const height = Math.round(Number(resolution.height));
  if (!Number.isFinite(width) || !Number.isFinite(height)) {
    return null;
  }
  return {
    width: clamp(width, EXPORT_MIN_DIMENSION, EXPORT_MAX_DIMENSION),
    height: clamp(height, EXPORT_MIN_DIMENSION, EXPORT_MAX_DIMENSION)
  };
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
    scalePercent: getSavedExportScalePercent(),
    resolutionLocked: state.exportResolutionLocked !== false,
    customResolution:
      state.exportResolutionLocked === false
        ? normalizeExportCustomResolution(state.exportCustomResolution)
        : null
  };
  scheduleSessionSave();
}

function clearRememberedExportSetup() {
  state.lastExportSetup = null;
  state.exportResolutionLocked = true;
  state.exportCustomResolution = null;
}

function getRememberedExportSetup() {
  if (!state.lastExportSetup || !state.lastExportSetup.selectionBounds) {
    return null;
  }

  const selectionBounds = normalizeExportSelectionBounds(state.lastExportSetup.selectionBounds);
  const scalePercent = Number(state.lastExportSetup.scalePercent);
  return {
    selectionBounds,
    scalePercent: Number.isFinite(scalePercent) && scalePercent > 0 ? scalePercent : 100,
    resolutionLocked: state.lastExportSetup.resolutionLocked !== false,
    customResolution: normalizeExportCustomResolution(state.lastExportSetup.customResolution)
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
    scalePercent: Number.isFinite(scalePercent) && scalePercent > 0 ? scalePercent : 100,
    resolutionLocked: setup.resolutionLocked !== false,
    customResolution: normalizeExportCustomResolution(setup.customResolution)
  };
}

function captureCurrentExportSetupSnapshot() {
  return normalizeExportSetupSnapshot({
    selectionBounds: state.exportSelectionBounds,
    scalePercent: state.exportScalePercent,
    resolutionLocked: state.exportResolutionLocked,
    customResolution: state.exportCustomResolution
  });
}

function exportHistoryNumbersEqual(left, right, epsilon = 0.001) {
  return Math.abs(Number(left) - Number(right)) <= epsilon;
}

function exportSelectionBoundsEqual(left, right) {
  if (!left || !right) {
    return left === right;
  }
  return (
    exportHistoryNumbersEqual(left.left, right.left) &&
    exportHistoryNumbersEqual(left.top, right.top) &&
    exportHistoryNumbersEqual(left.right, right.right) &&
    exportHistoryNumbersEqual(left.bottom, right.bottom)
  );
}

function exportCustomResolutionsEqual(left, right) {
  if (!left || !right) {
    return left === right;
  }
  return Number(left.width) === Number(right.width) && Number(left.height) === Number(right.height);
}

function exportSetupSnapshotsEqual(left, right) {
  if (!left || !right) {
    return left === right;
  }
  return (
    exportSelectionBoundsEqual(left.selectionBounds, right.selectionBounds) &&
    exportHistoryNumbersEqual(left.scalePercent, right.scalePercent) &&
    left.resolutionLocked === right.resolutionLocked &&
    exportCustomResolutionsEqual(left.customResolution, right.customResolution)
  );
}

function resetExportCropHistory() {
  state.exportCropHistory = [];
  state.exportCropRedoHistory = [];
}

function pushExportCropHistoryStep(beforeSetup, afterSetup, options = {}) {
  const before = normalizeExportSetupSnapshot(beforeSetup);
  const after = normalizeExportSetupSnapshot(afterSetup);
  if (
    !before ||
    !after ||
    exportSetupSnapshotsEqual(before, after) ||
    (options.requireBoundsChange &&
      exportSelectionBoundsEqual(before.selectionBounds, after.selectionBounds))
  ) {
    return false;
  }

  state.exportCropRedoHistory = [];
  state.exportCropHistory.push({ before, after });
  if (state.exportCropHistory.length > EXPORT_CROP_HISTORY_LIMIT) {
    state.exportCropHistory.splice(
      0,
      state.exportCropHistory.length - EXPORT_CROP_HISTORY_LIMIT
    );
  }
  return true;
}

function applyExportCropHistorySnapshot(snapshot) {
  const setup = normalizeExportSetupSnapshot(snapshot);
  if (!state.exportMode || state.exportTask || !setup) {
    return false;
  }

  state.exportSelectionBounds = { ...setup.selectionBounds };
  state.exportScalePercent = setup.scalePercent;
  state.exportResolutionLocked = setup.resolutionLocked;
  state.exportCustomResolution = setup.resolutionLocked
    ? null
    : normalizeExportCustomResolution(setup.customResolution);
  state.exportDrag = null;
  updateExportResolutionLockButtonsUI();
  updateExportOverlayGeometry();
  return true;
}

function undoExportCropAdjustment() {
  const action = state.exportCropHistory[state.exportCropHistory.length - 1];
  if (!action || !applyExportCropHistorySnapshot(action.before)) {
    return false;
  }
  state.exportCropHistory.pop();
  state.exportCropRedoHistory.push(action);
  return true;
}

function redoExportCropAdjustment() {
  const action = state.exportCropRedoHistory[state.exportCropRedoHistory.length - 1];
  if (!action || !applyExportCropHistorySnapshot(action.after)) {
    return false;
  }
  state.exportCropRedoHistory.pop();
  state.exportCropHistory.push(action);
  return true;
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
  if (document.activeElement !== exportWidthInput) {
    exportWidthInput.value = width;
  }
  if (document.activeElement !== exportHeightInput) {
    exportHeightInput.value = height;
  }
  if (exportSidebarWidthInput) {
    if (document.activeElement !== exportSidebarWidthInput) {
      exportSidebarWidthInput.value = width;
    }
  }
  if (exportSidebarHeightInput) {
    if (document.activeElement !== exportSidebarHeightInput) {
      exportSidebarHeightInput.value = height;
    }
  }
  updateExportResolutionLockButtonsUI();
}

function updateExportResolutionLockButtonsUI() {
  const locked = state.exportResolutionLocked !== false;
  const previewNeedsOutline =
    state.exportSeeBeyondEnabled === false ||
    isNearlyBlackHexColor(state.canvasBackgroundColor);
  if (exportOverlay) {
    exportOverlay.classList.toggle("has-light-crop-outline", previewNeedsOutline);
  }
  for (const button of [exportResolutionLockButton, exportSidebarResolutionLockButton]) {
    if (!button) {
      continue;
    }
    const isPreviewLock = button === exportResolutionLockButton;
    button.classList.toggle("is-unlocked", !locked);
    button.classList.toggle("has-light-outline", isPreviewLock && previewNeedsOutline);
    button.setAttribute("aria-pressed", String(locked));
    button.setAttribute("aria-label", locked ? "Unlock export aspect ratio" : "Lock export aspect ratio");
    button.title = locked ? "Unlock export aspect ratio" : "Lock export aspect ratio";
    button.disabled = Boolean(state.exportTask);
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

function getExportSequencePrewarmMs() {
  return Math.round(clamp(Number(state.exportSequencePrewarmSeconds) || 0, 0, 300) * 1000);
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
  if (exportSequencePrewarmInput) {
    exportSequencePrewarmInput.value = String(state.exportSequencePrewarmSeconds ?? 0);
    exportSequencePrewarmInput.disabled = Boolean(state.exportTask);
  }
  if (exportGifSizeLimitToggle) {
    exportGifSizeLimitToggle.checked = Boolean(state.exportGifSizeLimitEnabled);
    exportGifSizeLimitToggle.disabled = Boolean(state.exportTask);
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
  if (state.exportSelectionBounds && state.exportResolutionLocked === false) {
    state.exportCustomResolution = getExportScaledResolutionForScale(
      state.exportSelectionBounds,
      numericScale
    );
  } else {
    state.exportCustomResolution = null;
  }
  updateExportScaleButtonsUI();
  updateExportOverlayGeometry();
}

function resizeExportSelectionForUnlockedResolution(axis, currentResolution, nextResolution) {
  if (!state.exportSelectionBounds || !currentResolution || !nextResolution) {
    return;
  }

  const normalized = normalizeExportSelectionBounds(state.exportSelectionBounds);
  const currentDimension = axis === "height" ? currentResolution.height : currentResolution.width;
  const nextDimension = axis === "height" ? nextResolution.height : nextResolution.width;
  if (!Number.isFinite(currentDimension) || currentDimension <= 0 || !Number.isFinite(nextDimension)) {
    return;
  }

  const ratio = nextDimension / currentDimension;
  if (!Number.isFinite(ratio) || ratio <= 0) {
    return;
  }

  const nextBounds = { ...normalized };
  if (axis === "height") {
    const centerY = (normalized.top + normalized.bottom) / 2;
    const nextHeight = Math.max(EXPORT_MIN_SIZE, (normalized.bottom - normalized.top) * ratio);
    nextBounds.top = centerY - nextHeight / 2;
    nextBounds.bottom = centerY + nextHeight / 2;
  } else {
    const centerX = (normalized.left + normalized.right) / 2;
    const nextWidth = Math.max(EXPORT_MIN_SIZE, (normalized.right - normalized.left) * ratio);
    nextBounds.left = centerX - nextWidth / 2;
    nextBounds.right = centerX + nextWidth / 2;
  }
  state.exportSelectionBounds = normalizeExportSelectionBounds(nextBounds);
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
  const targetDimension = clamp(Math.round(requested), EXPORT_MIN_DIMENSION, EXPORT_MAX_DIMENSION);

  if (state.exportResolutionLocked === false) {
    const current = normalizeExportCustomResolution(state.exportCustomResolution) ||
      getExportScaledResolutionForScale(normalized, state.exportScalePercent);
    const nextResolution = normalizeExportCustomResolution({
      width: axis === "width" ? targetDimension : current.width,
      height: axis === "height" ? targetDimension : current.height
    });
    state.exportCustomResolution = nextResolution;
    resizeExportSelectionForUnlockedResolution(axis, current, nextResolution);
    if (nextResolution) {
      const nextBounds = normalizeExportSelectionBounds(state.exportSelectionBounds);
      const nextBase = getExportBaseResolution(nextBounds);
      const widthMultiplier = nextResolution.width / nextBase.width;
      state.exportScalePercent = clamp(
        widthMultiplier,
        getExportMinScaleMultiplier(nextBounds),
        getExportMaxScaleMultiplier(nextBounds)
      ) * 100;
    }
    updateExportScaleButtonsUI();
    updateExportOverlayGeometry();
    return;
  }

  state.exportCustomResolution = null;
  const sourceDimension = axis === "height" ? base.height : base.width;
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

function setExportResolutionLocked(locked) {
  if (!state.exportMode || !state.exportSelectionBounds || state.exportTask) {
    return;
  }

  const normalized = normalizeExportSelectionBounds(state.exportSelectionBounds);
  if (locked) {
    const current = normalizeExportCustomResolution(state.exportCustomResolution) ||
      getExportScaledResolution(normalized);
    state.exportResolutionLocked = true;
    state.exportCustomResolution = null;
    setExportResolutionFromInput("width", current.width);
    return;
  }

  state.exportResolutionLocked = false;
  state.exportCustomResolution = getExportScaledResolution(normalized);
  updateExportResolutionLockButtonsUI();
  updateExportOverlayGeometry();
}

function toggleExportResolutionLock() {
  setExportResolutionLocked(state.exportResolutionLocked === false);
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
  exportOverlay.classList.toggle("has-guidelines", Boolean(state.exportGuidelinesEnabled));

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
  updateExportResolutionLockButtonsUI();
  updateGifPauseButtonUI();
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
  resetExportCropHistory();
  state.exportMode = false;
  state.exportSelectionBounds = null;
  state.exportDrag = null;
  state.exportScalePercent = 100;
  updateExportModeUI();
  updateUndoState();
  scheduleSceneRendererEvaluation();
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

  if (state.sceneRendererActive || state.sceneRendererPreparing) {
    deactivateSceneRenderer();
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
  resetExportCropHistory();
  state.exportMode = true;
  state.exportSelectionBounds = remembered
    ? remembered.selectionBounds
    : computeInitialExportSelectionBounds();
  state.exportScalePercent = remembered ? remembered.scalePercent : 100;
  state.exportResolutionLocked = remembered ? remembered.resolutionLocked !== false : true;
  state.exportCustomResolution =
    remembered && state.exportResolutionLocked === false
      ? normalizeExportCustomResolution(remembered.customResolution)
      : null;
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
    originBounds: { ...state.exportSelectionBounds },
    originSetup: captureCurrentExportSetupSnapshot()
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
    const lockAspect = state.exportResolutionLocked !== false || Boolean(modifiers.shiftKey);
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
  if (state.exportDrag.mode !== "move") {
    state.exportCustomResolution = null;
  }
  updateExportOverlayGeometry();
}

function stopExportSelectionDrag(pointerId) {
  const drag = state.exportDrag;
  if (!drag || drag.pointerId !== pointerId) {
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
  pushExportCropHistoryStep(drag.originSetup, captureCurrentExportSetupSnapshot(), {
    requireBoundsChange: true
  });
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
  syncViewportPointerCursorClasses();
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

function getBrushPlacementSize(brush, options = {}) {
  if (!brush) {
    return { width: 0, height: 0 };
  }

  let width = 0;
  let height = 0;
  const useRandomSize = options.randomize === true && isRandomSizeEnabled();
  if (consistentToggle.checked) {
    if (isRandomSizeEnabled()) {
      const range = getActiveRandomSizeRange();
      const size = useRandomSize
        ? sampleRandomizedSizeValue(range)
        : (range.min + range.max) / 2;
      return getBrushSizeFromLongestSide(brush, size);
    } else {
      width = Math.max(4, Number(consistentSizeSlider.value));
    }
    height = Math.max(4, width * (brush.height / brush.width));
  } else {
    const sizePercent = isRandomSizeEnabled()
      ? (() => {
          const range = getActiveRandomSizeRange();
          return useRandomSize
            ? sampleRandomizedSizeValue(range)
            : (range.min + range.max) / 2;
        })()
      : Number(sizeSlider.value);
    const scale = sizePercent / 100;
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

function syncViewportPointerCursorClasses() {
  viewport.classList.toggle("is-drawing", Boolean(state.drawing || (state.shapeDraft && state.shapeDraft.pointerId !== null)));
  viewport.classList.toggle("is-erasing", Boolean(state.eraseMode));
  viewport.classList.toggle("is-panning", Boolean(state.panning || state.touchGesture));
  if (state.sidebarTab !== "edit" || state.panning || state.touchGesture) {
    viewport.classList.remove("is-edit-layer-clickable");
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
      !state.brushPickMode &&
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
  syncViewportPointerCursorClasses();
  updateBrushCursorPreview();
}

function cancelDrawingForGesture() {
  if (!state.drawing) {
    return;
  }

  const drawing = state.drawing;
  removeSceneRendererElements(drawing.stroke.elements);
  for (const element of drawing.stroke.elements) {
    unregisterStampSpatialCells(element);
    state.viewportRenderedStamps.delete(element);
    decrementUrlRef(element.dataset.brushUrl);
    removeSequencePixelateProxy(element);
    if (element.parentElement === world) {
      element.remove();
      state.stampCount = Math.max(0, state.stampCount - 1);
    }
  }
  if (viewport.hasPointerCapture(drawing.pointerId)) {
    viewport.releasePointerCapture(drawing.pointerId);
  }
  state.drawing = null;
  syncViewportPointerCursorClasses();
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
  syncViewportPointerCursorClasses();
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
  hideShapePreview();
  syncViewportPointerCursorClasses();
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
  cancelScheduledStrokeSequenceEffectRefresh(stroke);
  state.strokeById.delete(stroke.id);
  state.sequenceActiveStrokeIds.delete(stroke.id);
  const strokeIndex = state.strokes.indexOf(stroke);
  if (strokeIndex >= 0) {
    state.strokes.splice(strokeIndex, 1);
  }
}

function removeStampElementFromState(element, removalContext = null) {
  invalidateStampOcclusion();
  removeSceneRendererElements([element]);
  const strokeId = Number(element.dataset.strokeId);
  const stroke = Number.isFinite(strokeId) ? state.strokeById.get(strokeId) : null;
  const currentStrokeIndex = stroke ? state.strokes.indexOf(stroke) : -1;
  const currentStampIndex = stroke ? stroke.elements.indexOf(element) : -1;
  const strokeIndex =
    stroke && removalContext?.strokeOrder instanceof Map && removalContext.strokeOrder.has(stroke)
      ? Number(removalContext.strokeOrder.get(stroke))
      : currentStrokeIndex;
  const stampIndex =
    removalContext?.stampOrder instanceof Map && removalContext.stampOrder.has(element)
      ? Number(removalContext.stampOrder.get(element))
      : currentStampIndex;

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

  if (stroke && currentStampIndex >= 0) {
    stroke.elements.splice(currentStampIndex, 1);
    markStrokeSerializationDirty(stroke);
    invalidateStrokeSequenceTopology(stroke);
    if (!stroke.elements.length) {
      removeStrokeFromState(stroke);
    }
  }

  if (element.parentElement === world) {
    unregisterStampSpatialCells(element);
    state.viewportRenderedStamps.delete(element);
    decrementUrlRef(element.dataset.brushUrl);
    removeSequencePixelateProxy(element);
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
  sequenceSlotRuntimeStampCache.delete(element);
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
  sequenceSlotRuntimeStampCache.delete(stamp);
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

function createSequenceSlotRuntimeStamp(stamp, slotIndex) {
  let slots = sequenceSlotRuntimeStampCache.get(stamp);
  if (!slots) {
    slots = [];
    sequenceSlotRuntimeStampCache.set(stamp, slots);
  }
  if (slots[slotIndex]) {
    return slots[slotIndex];
  }
  const dataset = Object.create(null);
  for (const key of SEQUENCE_BASE_DATASET_KEYS) {
    if (Object.prototype.hasOwnProperty.call(stamp.dataset, key)) {
      dataset[key] = stamp.dataset[key];
    }
  }
  if (stamp.dataset.brushUrl) {
    dataset.brushUrl = stamp.dataset.brushUrl;
  }
  for (const key of SEQUENCE_SLOT_STATE_KEYS) {
    const slotKey = getSequenceSlotDatasetKey(slotIndex, key);
    if (Object.prototype.hasOwnProperty.call(stamp.dataset, slotKey)) {
      dataset[key] = stamp.dataset[slotKey];
    }
  }
  const runtimeStamp = { dataset };
  slots[slotIndex] = runtimeStamp;
  return runtimeStamp;
}

function commitSequenceSlotRuntimeStamp(stamp, slotIndex, runtimeStamp) {
  const dataset = runtimeStamp?.dataset;
  if (!dataset || typeof dataset !== "object") {
    return;
  }
  for (const key of SEQUENCE_SLOT_STATE_KEYS) {
    const slotKey = getSequenceSlotDatasetKey(slotIndex, key);
    if (Object.prototype.hasOwnProperty.call(dataset, key)) {
      const nextValue = String(dataset[key]);
      if (stamp.dataset[slotKey] !== nextValue) {
        stamp.dataset[slotKey] = nextValue;
      }
    } else if (Object.prototype.hasOwnProperty.call(stamp.dataset, slotKey)) {
      delete stamp.dataset[slotKey];
    }
  }
}

function cloneSequenceRuntime(runtime) {
  if (!runtime || typeof runtime !== "object") {
    return null;
  }
  const clone = { ...runtime };
  if (runtime.groupDataset && typeof runtime.groupDataset === "object") {
    clone.groupDataset = { ...runtime.groupDataset };
  }
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

function cloneLayerSequencePreviewSlots(slots) {
  if (!Array.isArray(slots)) {
    return null;
  }
  return slots.map((slotState) => {
    if (!slotState || !Array.isArray(slotState.buckets)) {
      return null;
    }
    return {
      ...slotState,
      buckets: slotState.buckets.map((bucket) => ({ ...bucket }))
    };
  });
}

function createLayerSequencePreviewExportSnapshot(stroke) {
  return cloneLayerSequencePreviewSlots(layerSequencePreviewRuntimeByStroke.get(stroke));
}

function restoreLayerSequencePreviewExportSnapshot(stroke, slots) {
  const restoredSlots = cloneLayerSequencePreviewSlots(slots);
  if (restoredSlots) {
    layerSequencePreviewRuntimeByStroke.set(stroke, restoredSlots);
  } else {
    layerSequencePreviewRuntimeByStroke.delete(stroke);
  }
}

function createSequenceExportSnapshot() {
  return state.strokes.map((stroke) => ({
    stroke,
    sequenceRuntime: cloneSequenceRuntime(stroke.sequenceRuntime),
    sequenceSlotRuntimes: Array.isArray(stroke.sequenceSlotRuntimes)
      ? stroke.sequenceSlotRuntimes.map(cloneSequenceRuntime)
      : null,
    sequencePauseStartTime: Number.isFinite(Number(stroke.sequencePauseStartTime))
      ? Number(stroke.sequencePauseStartTime)
      : null,
    sequencePreviewRuntime: createLayerSequencePreviewExportSnapshot(stroke),
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
        filter: element.style.filter,
        imageRendering: element.style.imageRendering
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
    if (Number.isFinite(strokeSnapshot.sequencePauseStartTime)) {
      strokeSnapshot.stroke.sequencePauseStartTime = strokeSnapshot.sequencePauseStartTime;
    } else {
      delete strokeSnapshot.stroke.sequencePauseStartTime;
    }
    restoreLayerSequencePreviewExportSnapshot(
      strokeSnapshot.stroke,
      strokeSnapshot.sequencePreviewRuntime
    );
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
      element.style.imageRendering = elementSnapshot.imageRendering || "";
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

async function prewarmSequencesForExport(prewarmMs, task = null) {
  const durationMs = Math.max(0, Math.round(Number(prewarmMs) || 0));
  runLayerSequences(0);
  if (!durationMs) {
    return;
  }

  const stepMs = 33;
  for (let timeMs = stepMs; timeMs < durationMs; timeMs += stepMs) {
    throwIfTaskCancelled(task);
    runLayerSequences(timeMs);
    if (timeMs % (stepMs * 8) === 0) {
      await yieldToMainThread(task);
    }
  }
  throwIfTaskCancelled(task);
  runLayerSequences(durationMs);
}

function getActiveSequenceStrokes() {
  if (state.gifAnimationsPaused || document.visibilityState === "hidden") {
    return [];
  }
  return state.strokes.filter((stroke) => {
    if (
      !stroke ||
      stroke.hidden ||
      isStrokeSequencePaused(stroke) ||
      !isLayerSequenceEnabled(stroke) ||
      !Array.isArray(stroke.elements)
    ) {
      return false;
    }
    return getLayerSequenceSlots(stroke).some((slot) =>
      isImplementedLayerSequenceEffect(slot.effect) &&
        stroke.elements.some((element) => element.parentElement === world)
    );
  });
}

function hasActiveSequenceEffectOnCanvas() {
  return getActiveSequenceStrokes().length > 0;
}

function getTrackedActiveSequenceStrokes() {
  const activeStrokes = [];
  for (const strokeId of state.sequenceActiveStrokeIds) {
    const stroke = state.strokeById.get(strokeId);
    if (stroke) {
      activeStrokes.push(stroke);
    }
  }
  return activeStrokes;
}

function getAdaptiveSequenceFrameIntervalMs(activeStrokes = null) {
  const strokes = Array.isArray(activeStrokes)
    ? activeStrokes
    : getTrackedActiveSequenceStrokes();
  let activeStampCount = 0;
  for (const stroke of strokes) {
    activeStampCount += Array.isArray(stroke?.elements) ? stroke.elements.length : 0;
  }
  if (activeStampCount >= 8000) {
    return 50;
  }
  if (activeStampCount >= 3000) {
    return 1000 / 30;
  }
  if (activeStampCount >= 1000) {
    return 25;
  }
  return 0;
}

function notifyStampLimitReached() {
  updateBrushStatus(
    `Canvas limit reached (${MAX_VISIBLE_STAMPS.toLocaleString()} images). Undo or clear to add more.`
  );
}

function normalizeStrokeLayerType(layerType) {
  if (
    layerType === "spray" ||
    layerType === "line" ||
    layerType === "box" ||
    layerType === "box-outline" ||
    layerType === "circle" ||
    layerType === "circle-outline"
  ) {
    return layerType;
  }
  return "stroke";
}

function normalizeLayerBlendMode(value) {
  const candidate = String(value || "normal");
  return LAYER_BLEND_MODE_OPTIONS.some((option) => option.value === candidate)
    ? candidate
    : "normal";
}

function getLayerBlendMode(stroke) {
  return normalizeLayerBlendMode(stroke?.blendMode);
}

function getStrokeById(strokeId) {
  const numericId = Number(strokeId);
  if (!Number.isFinite(numericId)) {
    return null;
  }
  return state.strokeById.get(numericId) ||
    state.strokes.find((stroke) => Number(stroke?.id) === numericId) ||
    null;
}

function getCanvasCompositeOperationForBlendMode(blendMode) {
  const normalized = normalizeLayerBlendMode(blendMode);
  return normalized === "normal" ? "source-over" : normalized;
}

function setLayerBlendMode(stroke, blendMode) {
  if (!stroke) {
    return;
  }
  stroke.blendMode = normalizeLayerBlendMode(blendMode);
  markStrokeSerializationDirty(stroke);
  applyStrokeBlendMode(stroke);
}

function applyStrokeBlendMode(stroke) {
  if (!stroke || !Array.isArray(stroke.elements)) {
    return;
  }
  invalidateStampOcclusion();
  const blendMode = getLayerBlendMode(stroke);
  const cssBlendMode = blendMode === "normal" ? "" : blendMode;
  for (const element of stroke.elements) {
    setInlineStyleIfChanged(element, "mixBlendMode", cssBlendMode);
    if (element.dataset.blendMode !== blendMode) {
      element.dataset.blendMode = blendMode;
    }
  }
  syncSceneRendererElements(stroke.elements);
}

function normalizeLayerSequenceValue(value, options) {
  const allowed = new Set(options.map((option) => option.value));
  const candidate = Array.isArray(value) ? value[0] : value;
  return allowed.has(String(candidate || "")) ? String(candidate) : options[0]?.value || "";
}

function normalizeLayerSequenceSlot(slot = {}) {
  const effect = normalizeLayerSequenceValue(
    slot.effect || slot.sequenceEffect || slot.sequenceEffects,
    LAYER_SEQUENCE_EFFECT_OPTIONS
  );
  return {
    effect,
    timingStyle: normalizeLayerSequenceTimingStyle(
      slot.timingStyle || slot.sequenceTimingStyle || slot.sequenceTimingStyles,
      effect
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
  markStrokeSerializationDirty(stroke);
}

function hasLayerSequenceEffectSlots(stroke) {
  return Boolean(
    stroke?.sequenceConfigured ||
    stroke?.sequenceEnabled === true ||
    getExtraLayerSequenceSlots(stroke).length
  );
}

function getLayerSequenceSlotCount(stroke) {
  return hasLayerSequenceEffectSlots(stroke)
    ? 1 + getExtraLayerSequenceSlots(stroke).length
    : 0;
}

function getLayerSequenceSlots(stroke) {
  if (!hasLayerSequenceEffectSlots(stroke)) {
    return [];
  }
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
    effect === "image-cycle" ||
    effect === "pixelate" ||
    effect === "blur"
  );
}

function isGroupedLayerSequenceEffect(effect) {
  return isImplementedLayerSequenceEffect(effect) &&
    !LAYER_SEQUENCE_GROUPED_EXCLUDED_EFFECTS.has(String(effect || ""));
}

function getLayerSequenceTimingOptionsForEffect(effect) {
  return LAYER_SEQUENCE_TIMING_OPTIONS.filter(
    (option) => option.value !== "grouped" || isGroupedLayerSequenceEffect(effect)
  );
}

function normalizeLayerSequenceTimingStyle(value, effect) {
  const candidate = Array.isArray(value) ? value[0] : value;
  if (String(candidate || "") === "grouped" && !isGroupedLayerSequenceEffect(effect)) {
    return "all";
  }
  return normalizeLayerSequenceValue(candidate, getLayerSequenceTimingOptionsForEffect(effect));
}

function getLayerSequenceSlot(stroke, slotIndex = 0) {
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, MAX_LAYER_SEQUENCE_EFFECTS - 1);
  if (safeSlotIndex <= 0) {
    const effect = normalizeLayerSequenceValue(
      stroke?.sequenceEffect || stroke?.sequenceEffects,
      LAYER_SEQUENCE_EFFECT_OPTIONS
    );
    return {
      effect,
      timingStyle: normalizeLayerSequenceTimingStyle(
        stroke?.sequenceTimingStyle || stroke?.sequenceTimingStyles,
        effect
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
  return normalizeLayerSequenceTimingStyle(
    stroke?.sequenceTimingStyle || stroke?.sequenceTimingStyles,
    getLayerSequenceEffect(stroke)
  );
}

function isLayerSequenceEnabled(stroke) {
  if (!stroke || stroke.sequenceUserDisabled === true) {
    return false;
  }
  return stroke.sequenceEnabled === true || hasLayerSequenceEffectSlots(stroke);
}

function setLayerSequenceValue(stroke, group, value, slotIndex = 0) {
  if (!stroke) {
    return;
  }
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, MAX_LAYER_SEQUENCE_EFFECTS - 1);
  const currentEffect = getLayerSequenceEffect(stroke, safeSlotIndex);
  const normalized = group === "timing"
    ? normalizeLayerSequenceTimingStyle(value, currentEffect)
    : normalizeLayerSequenceValue(value, LAYER_SEQUENCE_EFFECT_OPTIONS);
  if (safeSlotIndex > 0) {
    const extras = getExtraLayerSequenceSlots(stroke);
    const slot = normalizeLayerSequenceSlot(extras[safeSlotIndex - 1]);
    if (group === "timing") {
      slot.timingStyle = normalized;
    } else {
      slot.effect = normalized;
      slot.timingStyle = normalizeLayerSequenceTimingStyle(slot.timingStyle, slot.effect);
    }
    extras[safeSlotIndex - 1] = slot;
    setExtraLayerSequenceSlots(stroke, extras);
  } else if (group === "timing") {
    stroke.sequenceTimingStyle = normalized;
    delete stroke.sequenceTimingStyles;
  } else {
    stroke.sequenceEffect = normalized;
    delete stroke.sequenceEffects;
    stroke.sequenceTimingStyle = normalizeLayerSequenceTimingStyle(
      stroke.sequenceTimingStyle || stroke.sequenceTimingStyles,
      stroke.sequenceEffect
    );
    delete stroke.sequenceTimingStyles;
  }
  markStrokeSerializationDirty(stroke);
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
  normalized.pixelateAmount = Number.isFinite(Number(normalized.pixelateAmount))
    ? clamp(Math.round(Number(normalized.pixelateAmount)), 0, 64)
    : 16;
  normalized.pixelateSpeed = normalizeSequenceSpeedSliderValue(normalized.pixelateSpeed, 5000, 50, 45);
  normalized.blurAmount = Number.isFinite(Number(normalized.blurAmount))
    ? clamp(Math.round(Number(normalized.blurAmount)), 0, 64)
    : 8;
  normalized.blurSpeed = normalizeSequenceSpeedSliderValue(normalized.blurSpeed, 5000, 50, 45);
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
  normalized.stepRate = clamp(Math.round(Number(normalized.stepRate) || 350), 50, 4000);
  normalized.randomSpeed = normalizeSequenceSpeedSliderValue(normalized.randomSpeed, 4000, 50, 45);
  return normalized;
}

function setLayerSequenceSetting(stroke, key, rawValue, slotIndex = 0) {
  if (!stroke || !(key in LAYER_SEQUENCE_DEFAULT_SETTINGS)) {
    return;
  }
  stroke.sequenceConfigured = true;
  stroke.sequenceEnabled = true;
  stroke.sequenceUserDisabled = false;
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
  markStrokeSerializationDirty(stroke);
}

function createLayerSequenceSelect(stroke, group, options, slotIndex = 0) {
  const selectOptions = group === "timing"
    ? getLayerSequenceTimingOptionsForEffect(getLayerSequenceEffect(stroke, slotIndex))
    : options;
  const selectedValue = group === "timing"
    ? getLayerSequenceTimingStyle(stroke, slotIndex)
    : getLayerSequenceEffect(stroke, slotIndex);
  const select = document.createElement("select");
  select.className = "edit-layer-sequence-select";
  select.dataset.sequenceGroup = group;
  select.dataset.sequenceSlotIndex = String(slotIndex);
  select.setAttribute("aria-label", group === "timing" ? "Sequence style" : "Sequence effect");

  for (const option of selectOptions) {
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
  if (key === "randomSpeed") {
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

function getLayerBlendModeLabel(value) {
  const normalized = normalizeLayerBlendMode(value);
  return LAYER_BLEND_MODE_OPTIONS.find((option) => option.value === normalized)?.label || "Normal";
}

function inferStrokeOpacityPercent(stroke) {
  const elements = Array.isArray(stroke?.elements) ? stroke.elements : [];
  for (const element of elements) {
    const opacity = Number.isFinite(Number(element.dataset.sequenceBaseOpacity))
      ? Number(element.dataset.sequenceBaseOpacity)
      : Number(element.style.opacity);
    if (Number.isFinite(opacity)) {
      return Math.round(clamp(opacity, 0, 1) * 100);
    }
  }
  return 100;
}

function normalizeLayerOpacityPercent(value, fallback = 100) {
  const numericValue = value === null || value === "" ? NaN : Number(value);
  return clamp(Math.round(Number.isFinite(numericValue) ? numericValue : fallback), 0, 100);
}

function getLayerOpacityPercent(stroke) {
  return normalizeLayerOpacityPercent(stroke?.layerOpacity, inferStrokeOpacityPercent(stroke));
}

function getLayerOpacityFraction(stroke) {
  return getLayerOpacityPercent(stroke) / 100;
}

function normalizeLayerScaleValue(value) {
  return clamp(Math.round(Number.isFinite(Number(value)) ? Number(value) : 0), -1000, 1000);
}

function getLayerScaleValue(stroke) {
  return normalizeLayerScaleValue(stroke?.layerScale);
}

function getLayerScaleFactor(stroke) {
  const value = getLayerScaleValue(stroke);
  if (value >= 0) {
    return 1 + value / 100;
  }
  return 1 / (1 + Math.abs(value) / 100);
}

function normalizeLayerRotationDegrees(value) {
  return clamp(Math.round(Number.isFinite(Number(value)) ? Number(value) : 0), -360, 360);
}

function getLayerRotationDegrees(stroke) {
  return normalizeLayerRotationDegrees(stroke?.layerRotation);
}

function getLayerScaleDisplayValue(stroke) {
  return `${Math.round(getLayerScaleFactor(stroke) * 100)}%`;
}

function getLayerControlDisplayValue(stroke, key) {
  if (key === "layerOpacity") {
    return `${getLayerOpacityPercent(stroke)}%`;
  }
  if (key === "layerScale") {
    return getLayerScaleDisplayValue(stroke);
  }
  if (key === "layerRotation") {
    return `${getLayerRotationDegrees(stroke)}deg`;
  }
  return "";
}

const strokeLayerBoundsCache = new WeakMap();

function getStrokeLayerBounds(stroke) {
  const elements = Array.isArray(stroke?.elements) ? stroke.elements : [];
  const revision = Number(stroke?.serializationRevision) || 0;
  const cached = strokeLayerBoundsCache.get(stroke);
  if (
    cached &&
    cached.revision === revision &&
    cached.elements === elements &&
    cached.length === elements.length
  ) {
    return cached.bounds;
  }
  let left = Infinity;
  let top = Infinity;
  let right = -Infinity;
  let bottom = -Infinity;
  for (const element of elements) {
    const elementLeft = parseFloat(element.style.left) || 0;
    const elementTop = parseFloat(element.style.top) || 0;
    const width = Math.max(0, parseFloat(element.style.width) || 0);
    const height = Math.max(0, parseFloat(element.style.height) || 0);
    if (width <= 0 || height <= 0) {
      continue;
    }
    left = Math.min(left, elementLeft);
    top = Math.min(top, elementTop);
    right = Math.max(right, elementLeft + width);
    bottom = Math.max(bottom, elementTop + height);
  }
  if (!Number.isFinite(left) || !Number.isFinite(top) || !Number.isFinite(right) || !Number.isFinite(bottom)) {
    if (stroke && typeof stroke === "object") {
      strokeLayerBoundsCache.set(stroke, {
        revision,
        elements,
        length: elements.length,
        bounds: null
      });
    }
    return null;
  }
  const bounds = { left, top, right, bottom };
  if (stroke && typeof stroke === "object") {
    strokeLayerBoundsCache.set(stroke, {
      revision,
      elements,
      length: elements.length,
      bounds
    });
  }
  return bounds;
}

function getStampLayerTransform(stroke, element) {
  const scale = getLayerScaleFactor(stroke);
  const rotation = getLayerRotationDegrees(stroke);
  if (!stroke || !element || (Math.abs(scale - 1) < 0.0001 && rotation === 0)) {
    return { x: 0, y: 0, rotation, scale };
  }
  const bounds = getStrokeLayerBounds(stroke);
  if (!bounds) {
    return { x: 0, y: 0, rotation, scale };
  }
  const layerCenterX = (bounds.left + bounds.right) / 2;
  const layerCenterY = (bounds.top + bounds.bottom) / 2;
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  const centerX = left + width / 2;
  const centerY = top + height / 2;
  const dx = (centerX - layerCenterX) * scale;
  const dy = (centerY - layerCenterY) * scale;
  const radians = (rotation * Math.PI) / 180;
  const transformedCenterX = layerCenterX + dx * Math.cos(radians) - dy * Math.sin(radians);
  const transformedCenterY = layerCenterY + dx * Math.sin(radians) + dy * Math.cos(radians);
  return {
    x: transformedCenterX - centerX,
    y: transformedCenterY - centerY,
    rotation,
    scale
  };
}

function getStampGroupedLayerTransform(stroke, element, groupedTransform = null) {
  const groupMoveX = Number(groupedTransform?.moveX) || 0;
  const groupMoveY = Number(groupedTransform?.moveY) || 0;
  const groupRotation = Number(groupedTransform?.rotationOffset) || 0;
  const groupScale = Number.isFinite(Number(groupedTransform?.scale))
    ? Math.max(0.001, Number(groupedTransform.scale))
    : 1;
  const scale = getLayerScaleFactor(stroke) * groupScale;
  const rotation = getLayerRotationDegrees(stroke) + groupRotation;
  if (!stroke || !element) {
    return { x: groupMoveX, y: groupMoveY, rotation, scale };
  }
  const bounds = getStrokeLayerBounds(stroke);
  if (!bounds) {
    return { x: groupMoveX, y: groupMoveY, rotation, scale };
  }
  const layerCenterX = (bounds.left + bounds.right) / 2;
  const layerCenterY = (bounds.top + bounds.bottom) / 2;
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const width = Math.max(0, parseFloat(element.style.width) || 0);
  const height = Math.max(0, parseFloat(element.style.height) || 0);
  const centerX = left + width / 2;
  const centerY = top + height / 2;
  const dx = (centerX - layerCenterX) * scale;
  const dy = (centerY - layerCenterY) * scale;
  const radians = (rotation * Math.PI) / 180;
  const transformedCenterX = layerCenterX + groupMoveX + dx * Math.cos(radians) - dy * Math.sin(radians);
  const transformedCenterY = layerCenterY + groupMoveY + dx * Math.sin(radians) + dy * Math.cos(radians);
  return {
    x: transformedCenterX - centerX,
    y: transformedCenterY - centerY,
    rotation,
    scale
  };
}

function syncStrokeLayerOpacityBase(stroke) {
  if (!stroke || !Array.isArray(stroke.elements)) {
    return;
  }
  const opacity = String(getLayerOpacityFraction(stroke));
  for (const element of stroke.elements) {
    element.dataset.sequenceBaseOpacity = opacity;
  }
}

function applyStampLayerVisualStyle(stroke, stamp, visual = null) {
  if (!stamp) {
    return;
  }
  const layerTransform = visual?.groupedTransform
    ? getStampGroupedLayerTransform(stroke, stamp, visual.groupedTransform)
    : getStampLayerTransform(stroke, stamp);
  const baseRotation = Number(stamp.dataset.rotation) || 0;
  const opacity = Number.isFinite(Number(visual?.opacity))
    ? Number(visual.opacity)
    : getLayerOpacityFraction(stroke);
  const moveX = layerTransform.x + (Number(visual?.moveX) || 0);
  const moveY = layerTransform.y + (Number(visual?.moveY) || 0);
  const rotation = baseRotation + layerTransform.rotation + (Number(visual?.rotationOffset) || 0);
  const scale = layerTransform.scale * (Number(visual?.scale) || 1);
  setInlineStyleIfChanged(stamp, "opacity", String(clamp(opacity, 0, 1)));
  setInlineStyleIfChanged(
    stamp,
    "transform",
    `translate(${moveX}px, ${moveY}px) rotate(${rotation}deg) scale(${scale})`
  );
}

function applyStrokeLayerVisuals(stroke) {
  if (!stroke || !Array.isArray(stroke.elements)) {
    return;
  }
  invalidateStampOcclusion();
  syncStrokeLayerOpacityBase(stroke);
  for (const element of stroke.elements) {
    applyStampLayerVisualStyle(stroke, element);
    unregisterStampSpatialCells(element);
    if (!stroke.hidden && element.parentElement === world) {
      registerStampSpatialCells(element);
    } else {
      cacheStampWorldBounds(element);
    }
  }
  scheduleStampVisibilityRefresh();
  syncSceneRendererElements(stroke.elements);
}

function setLayerControlValue(stroke, key, value) {
  if (!stroke) {
    return;
  }
  if (key === "layerOpacity") {
    stroke.layerOpacity = normalizeLayerOpacityPercent(value, getLayerOpacityPercent(stroke));
    syncStrokeLayerOpacityBase(stroke);
  } else if (key === "layerScale") {
    stroke.layerScale = normalizeLayerScaleValue(value);
  } else if (key === "layerRotation") {
    stroke.layerRotation = normalizeLayerRotationDegrees(value);
  }
  markStrokeSerializationDirty(stroke);
  applyStrokeLayerVisuals(stroke);
}

function createLayerRangeControl(stroke, key, label, min, max, step) {
  const field = document.createElement("label");
  field.className = "edit-layer-property-row";

  const labelText = document.createElement("span");
  labelText.className = "edit-layer-property-label";
  labelText.textContent = label;

  const value = document.createElement("span");
  value.className = "edit-layer-property-value";
  value.textContent = getLayerControlDisplayValue(stroke, key);

  const input = document.createElement("input");
  input.type = "range";
  input.className = "edit-layer-property-input";
  input.dataset.layerSetting = key;
  input.min = String(min);
  input.max = String(max);
  input.step = String(step);
  input.value = key === "layerOpacity"
    ? String(getLayerOpacityPercent(stroke))
    : key === "layerScale"
    ? String(getLayerScaleValue(stroke))
    : String(getLayerRotationDegrees(stroke));

  field.appendChild(labelText);
  field.appendChild(value);
  field.appendChild(input);
  return field;
}

function createLayerFreezeControl(stroke) {
  const row = document.createElement("div");
  row.className = "edit-layer-property-row edit-layer-freeze-row";

  const inputId = `editLayerFreeze-${stroke.id}`;
  const labelText = document.createElement("label");
  labelText.className = "edit-layer-property-label";
  labelText.htmlFor = inputId;
  labelText.textContent = "freeze?";

  const value = document.createElement("span");
  value.className = "edit-layer-property-value";
  value.setAttribute("aria-hidden", "true");

  const switchLabel = document.createElement("label");
  switchLabel.className = "ios-switch edit-layer-freeze-switch";
  switchLabel.htmlFor = inputId;

  const input = document.createElement("input");
  input.id = inputId;
  input.type = "checkbox";
  input.className = "edit-layer-freeze-input";
  input.checked = Boolean(stroke.animationPaused);
  input.setAttribute("aria-label", "Freeze layer animation");

  const slider = document.createElement("span");
  slider.className = "ios-switch-slider";
  slider.setAttribute("aria-hidden", "true");

  switchLabel.appendChild(input);
  switchLabel.appendChild(slider);
  row.appendChild(labelText);
  row.appendChild(value);
  row.appendChild(switchLabel);
  return row;
}

function createLayerPropertyControls(stroke) {
  const panel = document.createElement("div");
  panel.className = "edit-layer-property-controls";
  panel.dataset.strokeId = String(stroke.id);
  panel.appendChild(createLayerRangeControl(stroke, "layerOpacity", "opacity", 0, 100, 1));
  panel.appendChild(createLayerRangeControl(stroke, "layerScale", "scale", -1000, 1000, 1));
  panel.appendChild(createLayerRangeControl(stroke, "layerRotation", "rotation", -360, 360, 1));
  panel.appendChild(createLayerFreezeControl(stroke));
  return panel;
}

function createLayerBlendModeControl(stroke) {
  const row = document.createElement("div");
  row.className = "edit-layer-blend-row";
  row.dataset.strokeId = String(stroke.id);

  const label = document.createElement("span");
  label.className = "edit-layer-sequence-label";
  label.textContent = "blend mode";

  const selectedValue = getLayerBlendMode(stroke);
  const menu = document.createElement("div");
  menu.className = "edit-layer-blend-menu";
  menu.dataset.strokeId = String(stroke.id);
  menu.dataset.originalBlendMode = selectedValue;

  const button = document.createElement("button");
  button.type = "button";
  button.className = "edit-layer-blend-button";
  button.dataset.layerAction = "blend-menu";
  button.setAttribute("aria-haspopup", "listbox");
  button.setAttribute("aria-expanded", "false");
  button.textContent = getLayerBlendModeLabel(selectedValue);
  button.addEventListener("click", (event) => {
    event.preventDefault();
    event.stopPropagation();
    if (menu.classList.contains("is-open")) {
      closeLayerBlendMenu(menu, true);
    } else {
      openLayerBlendMenu(menu, stroke);
    }
    state.selectedEditLayerId = stroke.id;
  });

  const optionsList = document.createElement("div");
  optionsList.className = "edit-layer-blend-options";
  optionsList.setAttribute("role", "listbox");
  optionsList.hidden = true;
  for (const option of LAYER_BLEND_MODE_OPTIONS) {
    const optionNode = document.createElement("button");
    optionNode.type = "button";
    optionNode.className = "edit-layer-blend-option";
    optionNode.dataset.blendMode = option.value;
    optionNode.setAttribute("role", "option");
    optionNode.setAttribute("aria-selected", String(option.value === selectedValue));
    optionNode.textContent = option.label;
    optionNode.classList.toggle("is-selected", option.value === selectedValue);
    optionNode.addEventListener("pointerover", () => {
      if (!menu.classList.contains("is-open")) {
        return;
      }
      setLayerBlendMode(stroke, option.value);
      for (const previewOption of menu.querySelectorAll(".edit-layer-blend-option.is-preview")) {
        previewOption.classList.remove("is-preview");
      }
      optionNode.classList.add("is-preview");
    });
    optionNode.addEventListener("click", (event) => {
      event.preventDefault();
      event.stopPropagation();
      setLayerBlendMode(stroke, option.value);
      menu.dataset.originalBlendMode = option.value;
      updateLayerBlendMenuSelection(menu, option.value);
      closeLayerBlendMenu(menu, false);
      state.selectedEditLayerId = stroke.id;
      scheduleSessionSave();
    });
    optionsList.appendChild(optionNode);
  }
  menu.appendChild(button);
  menu.appendChild(optionsList);
  row.appendChild(label);
  row.appendChild(menu);
  return row;
}

function closeLayerBlendMenu(menu, restorePreview = true) {
  if (!menu || !menu.classList.contains("is-open")) {
    return;
  }
  if (restorePreview) {
    const stroke = getStrokeById(menu.dataset.strokeId);
    if (stroke) {
      setLayerBlendMode(stroke, menu.dataset.originalBlendMode || "normal");
    }
  }
  menu.classList.remove("is-open");
  const button = menu.querySelector(".edit-layer-blend-button");
  const optionsList = menu.querySelector(".edit-layer-blend-options");
  if (button) {
    button.setAttribute("aria-expanded", "false");
  }
  if (optionsList) {
    optionsList.hidden = true;
  }
  for (const option of menu.querySelectorAll(".edit-layer-blend-option.is-preview")) {
    option.classList.remove("is-preview");
  }
}

function closeAllLayerBlendMenus(exceptMenu = null, restorePreview = true) {
  if (!editLayerList) {
    return;
  }
  for (const menu of editLayerList.querySelectorAll(".edit-layer-blend-menu.is-open")) {
    if (menu !== exceptMenu) {
      closeLayerBlendMenu(menu, restorePreview);
    }
  }
}

function openLayerBlendMenu(menu, stroke) {
  if (!menu || !stroke) {
    return;
  }
  closeAllLayerBlendMenus(menu, true);
  const currentBlendMode = getLayerBlendMode(stroke);
  menu.dataset.originalBlendMode = currentBlendMode;
  menu.classList.add("is-open");
  const button = menu.querySelector(".edit-layer-blend-button");
  const optionsList = menu.querySelector(".edit-layer-blend-options");
  if (button) {
    button.setAttribute("aria-expanded", "true");
  }
  if (optionsList) {
    optionsList.hidden = false;
  }
}

function updateLayerBlendMenuSelection(menu, blendMode) {
  if (!menu) {
    return;
  }
  const normalized = normalizeLayerBlendMode(blendMode);
  const button = menu.querySelector(".edit-layer-blend-button");
  if (button) {
    button.textContent = getLayerBlendModeLabel(normalized);
  }
  for (const option of menu.querySelectorAll(".edit-layer-blend-option")) {
    const selected = option.dataset.blendMode === normalized;
    option.classList.toggle("is-selected", selected);
    option.setAttribute("aria-selected", String(selected));
  }
}

function getLayerSequencePreviewBucketCount(total) {
  return Math.min(
    LAYER_SEQUENCE_PREVIEW_MAX_BUCKETS,
    Math.max(1, Math.floor(Number(total)) || 1)
  );
}

function getLayerSequencePreviewSlotState(stroke, slotIndex, total, effect, timingStyle) {
  if (!stroke || typeof stroke !== "object") {
    return null;
  }
  let slots = layerSequencePreviewRuntimeByStroke.get(stroke);
  if (!slots) {
    slots = [];
    layerSequencePreviewRuntimeByStroke.set(stroke, slots);
  }
  const safeSlotIndex = clamp(
    Math.floor(Number(slotIndex)) || 0,
    0,
    MAX_LAYER_SEQUENCE_EFFECTS - 1
  );
  const safeTotal = Math.max(0, Math.floor(Number(total)) || 0);
  const bucketCount = getLayerSequencePreviewBucketCount(safeTotal);
  const signature = `${safeTotal}:${effect}:${timingStyle}`;
  let slotState = slots[safeSlotIndex];
  if (!slotState || slotState.signature !== signature) {
    slotState = {
      signature,
      total: safeTotal,
      effect,
      timingStyle,
      decayMs: null,
      pausedAt: null,
      buckets: Array.from({ length: bucketCount }, () => ({
        key: "",
        firedAt: -Infinity,
        decayMs: LAYER_SEQUENCE_PREVIEW_MIN_DECAY_MS,
        effectDuration: 1
      }))
    };
    slots[safeSlotIndex] = slotState;
  }
  return slotState;
}

function getLayerSequencePreviewDecayMs(timingStyle, effectDuration, settings) {
  let duration = Math.sqrt(Math.max(1, Number(effectDuration) || 1)) * 18;
  if (timingStyle === "pulse") {
    duration = getPulseSpacingMs(settings) * 2.2;
  } else if (timingStyle === "wave") {
    duration = getWaveSpacingMs(settings) * 1.25;
  } else if (timingStyle === "step") {
    duration = Math.max(1, Number(settings.stepLength) || 1) * 0.75;
  } else if (timingStyle === "random") {
    duration = getRandomIntervalMs(settings) * 0.75;
  }
  return Math.round(clamp(
    duration,
    LAYER_SEQUENCE_PREVIEW_MIN_DECAY_MS,
    LAYER_SEQUENCE_PREVIEW_MAX_DECAY_MS
  ));
}

function createLayerSequencePreviewCapture(
  stroke,
  slotIndex,
  total,
  effect,
  timingStyle,
  settings,
  effectDuration
) {
  if (!stroke || state.sequenceExportActive) {
    return null;
  }
  const slotState = getLayerSequencePreviewSlotState(
    stroke,
    slotIndex,
    total,
    effect,
    timingStyle
  );
  if (!slotState) {
    return null;
  }
  if (!Number.isFinite(slotState.decayMs)) {
    slotState.decayMs = getLayerSequencePreviewDecayMs(
      timingStyle,
      effectDuration,
      settings
    );
  }
  return {
    slotState,
    total: Math.max(1, Math.floor(Number(total)) || 1),
    effectDuration: Math.max(1, Number(effectDuration) || 1),
    recordedKeysByBucket: Array(slotState.buckets.length).fill("")
  };
}

function claimLayerSequencePreviewImpulse(capture, index, trigger, activateAll = false) {
  if (!capture?.slotState || !trigger?.key) {
    return false;
  }
  if (activateAll) {
    return true;
  }
  const safeIndex = clamp(Math.floor(Number(index)) || 0, 0, capture.total - 1);
  const bucketCount = capture.slotState.buckets.length;
  const bucketIndex = Math.min(
    bucketCount - 1,
    Math.floor((safeIndex * bucketCount) / capture.total)
  );
  if (
    capture.recordedKeysByBucket[bucketIndex] === trigger.key ||
    capture.slotState.buckets[bucketIndex]?.key === trigger.key
  ) {
    return false;
  }
  capture.recordedKeysByBucket[bucketIndex] = trigger.key;
  return true;
}

function updateLayerSequencePreviewBucket(bucket, key, firedAt, decayMs, effectDuration) {
  if (!bucket || bucket.key === key) {
    return;
  }
  bucket.key = key;
  bucket.firedAt = firedAt;
  bucket.decayMs = decayMs;
  bucket.effectDuration = effectDuration;
}

function recordLayerSequencePreviewImpulse(
  capture,
  index,
  trigger,
  now,
  activateAll = false
) {
  if (!capture?.slotState || !trigger?.key) {
    return;
  }
  const { slotState, total, effectDuration } = capture;
  const frameTime = Number.isFinite(Number(now)) ? Number(now) : performance.now();
  const rawTriggerStartTime = Number.isFinite(Number(trigger.startTime))
    ? Number(trigger.startTime)
    : frameTime;
  const firedAt = Math.min(
    frameTime,
    rawTriggerStartTime - SEQUENCE_TRIGGER_PRIME_MS
  );
  const decayMs = slotState.decayMs;
  const bucketCount = slotState.buckets.length;
  if (activateAll) {
    for (const bucket of slotState.buckets) {
      updateLayerSequencePreviewBucket(
        bucket,
        trigger.key,
        firedAt,
        decayMs,
        effectDuration
      );
    }
    return;
  }
  const safeIndex = clamp(Math.floor(Number(index)) || 0, 0, total - 1);
  const bucketIndex = Math.min(
    bucketCount - 1,
    Math.floor((safeIndex * bucketCount) / total)
  );
  updateLayerSequencePreviewBucket(
    slotState.buckets[bucketIndex],
    trigger.key,
    firedAt,
    decayMs,
    effectDuration
  );
}

function createLayerSequencePreview(stroke, slotIndex = 0) {
  const preview = document.createElement("div");
  preview.className = "edit-layer-sequence-preview";
  preview.dataset.strokeId = String(stroke.id);
  preview.dataset.sequenceSlotIndex = String(slotIndex);
  preview.setAttribute("role", "img");
  preview.title = "Live trigger impulses across this layer's stamp sequence";

  const canvas = document.createElement("canvas");
  canvas.className = "edit-layer-sequence-preview-canvas";
  canvas.setAttribute("aria-hidden", "true");

  preview.appendChild(canvas);
  return preview;
}

function getLayerSequencePreviewPlaybackState(stroke) {
  if (!isLayerSequenceEnabled(stroke)) {
    return "disabled";
  }
  if (stroke?.hidden) {
    return "hidden";
  }
  if (
    document.visibilityState === "hidden" ||
    isStrokeSequencePaused(stroke) ||
    Number.isFinite(Number(stroke?.sequencePauseStartTime))
  ) {
    return "paused";
  }
  return "playing";
}

function setLayerSequencePreviewDataset(preview, key, value) {
  const nextValue = String(value);
  if (preview.dataset[key] !== nextValue) {
    preview.dataset[key] = nextValue;
  }
}

function drawLayerSequencePreviewMarker(
  context,
  x,
  y,
  effect,
  level,
  phase,
  settings,
  reducedMotion
) {
  const active = level > 0;
  const accent = effect === "color-cycle"
    ? normalizeHexColor(settings.colorCycleColor, "#ff00ff")
    : "#111111";
  let size = active ? 2.4 + level * 2 : 1.7;
  let offsetX = 0;
  let offsetY = 0;
  if (active && effect === "scale") {
    size *= 1 + Math.min(1.25, Math.max(0, Number(settings.scaleAmount) || 0) / 240);
  }
  if (active && effect === "move" && !reducedMotion) {
    const distance = 1.5 + level * 2.5;
    if (settings.moveMode === "left") {
      offsetX = -distance;
    } else if (settings.moveMode === "right") {
      offsetX = distance;
    } else if (settings.moveMode === "up") {
      offsetY = -distance;
    } else if (settings.moveMode === "down") {
      offsetY = distance;
    } else {
      offsetX = Math.cos(phase * Math.PI * 2) * distance;
      offsetY = Math.sin(phase * Math.PI * 2) * distance;
    }
  }

  context.save();
  context.translate(x + offsetX, y + offsetY);
  context.globalAlpha = active ? 0.5 + level * 0.5 : 0.38;
  context.fillStyle = active ? accent : "#777777";
  context.strokeStyle = "#111111";
  context.lineWidth = 1;
  if (active && effect === "blur") {
    context.shadowColor = accent;
    context.shadowBlur = 3 + level * 5;
  }
  if (effect === "pixelate") {
    context.fillRect(-size, -size, size * 2, size * 2);
  } else if (effect === "image-cycle") {
    context.rotate(active && !reducedMotion ? phase * Math.PI * 0.5 : Math.PI * 0.25);
    context.fillRect(-size, -size, size * 2, size * 2);
  } else if (effect === "rotate") {
    context.rotate(active && !reducedMotion
      ? phase * Math.PI * 2 * (settings.rotateReverse ? -1 : 1)
      : Math.PI * 0.25);
    context.fillRect(-size, -size, size * 2, size * 2);
  } else {
    context.beginPath();
    context.arc(0, 0, size, 0, Math.PI * 2);
    context.fill();
  }
  if (active && effect === "color-cycle") {
    context.globalAlpha = 0.8;
    context.stroke();
  }
  context.restore();

  if (active && !reducedMotion) {
    context.save();
    context.globalAlpha = level * 0.42;
    context.strokeStyle = accent;
    context.lineWidth = 1;
    context.beginPath();
    context.arc(x + offsetX, y + offsetY, size + (1 - level) * 5 + 2, 0, Math.PI * 2);
    context.stroke();
    context.restore();
  }
}

function paintLayerSequencePreview(preview, stroke, slotIndex, now) {
  const canvas = preview.querySelector(".edit-layer-sequence-preview-canvas");
  const context = canvas?.getContext("2d");
  if (!canvas || !context) {
    return;
  }
  const slot = getLayerSequenceSlot(stroke, slotIndex);
  const effect = slot.effect;
  const timingStyle = slot.timingStyle;
  const settings = normalizeLayerSequenceSettings(slot.settings);
  const total = Math.max(0, Array.isArray(stroke.elements) ? stroke.elements.length : 0);
  const slotState = getLayerSequencePreviewSlotState(
    stroke,
    slotIndex,
    total,
    effect,
    timingStyle
  );
  const playbackState = getLayerSequencePreviewPlaybackState(stroke);
  const isPlaying = playbackState === "playing";
  const pauseStartTime = Number(stroke.sequencePauseStartTime);
  if (playbackState === "paused" && slotState.pausedAt === null) {
    slotState.pausedAt = Number.isFinite(pauseStartTime) ? pauseStartTime : now;
  } else if (playbackState !== "paused") {
    slotState.pausedAt = null;
  }
  const displayTime = playbackState === "paused" && slotState.pausedAt !== null
    ? slotState.pausedAt
    : now;
  const effectLabel = LAYER_SEQUENCE_EFFECT_OPTIONS.find((option) => option.value === effect)?.label || effect;
  const timingLabel = LAYER_SEQUENCE_TIMING_OPTIONS.find((option) => option.value === timingStyle)?.label || timingStyle;
  const countText = `${total} stamp${total === 1 ? "" : "s"}`;
  const ariaLabel = `${effectLabel} ${timingLabel} trigger timeline across ${countText}` +
    (isPlaying ? "" : `, ${playbackState}`);
  if (preview.getAttribute("aria-label") !== ariaLabel) {
    preview.setAttribute("aria-label", ariaLabel);
  }
  preview.classList.toggle("is-inactive", !isPlaying);
  preview.classList.toggle("is-paused", playbackState === "paused");
  preview.classList.toggle("is-hidden", playbackState === "hidden");
  setLayerSequencePreviewDataset(preview, "effect", effect);
  setLayerSequencePreviewDataset(preview, "timingStyle", timingStyle);
  setLayerSequencePreviewDataset(preview, "total", total);
  setLayerSequencePreviewDataset(preview, "bucketCount", slotState.buckets.length);
  setLayerSequencePreviewDataset(preview, "playbackState", playbackState);

  const width = Math.max(1, Math.round(canvas.clientWidth));
  const height = Math.max(1, Math.round(canvas.clientHeight));
  if (width <= 1 || height <= 1) {
    return;
  }
  const pixelRatio = Math.min(2, Math.max(1, Number(window.devicePixelRatio) || 1));
  const renderWidth = Math.round(width * pixelRatio);
  const renderHeight = Math.round(height * pixelRatio);
  if (canvas.width !== renderWidth || canvas.height !== renderHeight) {
    canvas.width = renderWidth;
    canvas.height = renderHeight;
  }
  context.setTransform(pixelRatio, 0, 0, pixelRatio, 0, 0);
  context.clearRect(0, 0, width, height);

  const reducedMotion = Boolean(layerSequencePreviewReducedMotionQuery?.matches);
  const left = 14;
  const right = Math.max(left, width - 14);
  const centerY = Math.round(height / 2);
  const bucketCount = slotState.buckets.length;
  const positionForBucket = (index) => bucketCount <= 1
    ? (left + right) / 2
    : left + ((right - left) * index) / (bucketCount - 1);
  const visuals = slotState.buckets.map((bucket) => {
    const age = displayTime - bucket.firedAt;
    const impulseActive = Number.isFinite(age) && age >= 0 && age < bucket.decayMs;
    const impulseLevel = impulseActive
      ? reducedMotion
        ? 1
        : 1 - age / Math.max(1, bucket.decayMs)
      : 0;
    const effectActive = Number.isFinite(age) && age >= 0 && age < bucket.effectDuration;
    return {
      level: clamp(Math.max(impulseLevel, effectActive ? 0.14 : 0), 0, 1),
      phase: clamp(age / Math.max(1, bucket.effectDuration), 0, 1)
    };
  });

  context.save();
  context.strokeStyle = isPlaying ? "#b5b5b5" : "#d0d0d0";
  context.lineWidth = 1;
  context.beginPath();
  context.moveTo(left, centerY + 0.5);
  context.lineTo(right, centerY + 0.5);
  context.stroke();
  context.restore();

  const activeBuckets = [];
  for (let index = 0; index < bucketCount; index += 1) {
    const visual = visuals[index];
    if (visual.level <= 0) {
      continue;
    }
    activeBuckets.push(index);
    const x = positionForBucket(index);
    const previousX = index > 0 ? positionForBucket(index - 1) : x;
    const nextX = index < bucketCount - 1 ? positionForBucket(index + 1) : x;
    context.save();
    context.globalAlpha = 0.2 + visual.level * 0.55;
    context.strokeStyle = effect === "color-cycle"
      ? normalizeHexColor(settings.colorCycleColor, "#ff00ff")
      : "#111111";
    context.lineWidth = 1 + visual.level;
    context.beginPath();
    context.moveTo((previousX + x) / 2, centerY + 0.5);
    context.lineTo((nextX + x) / 2, centerY + 0.5);
    context.stroke();
    context.restore();
  }

  for (let index = 0; index < bucketCount; index += 1) {
    const visual = visuals[index];
    drawLayerSequencePreviewMarker(
      context,
      positionForBucket(index),
      centerY,
      effect,
      visual.level,
      visual.phase,
      settings,
      reducedMotion
    );
  }
  setLayerSequencePreviewDataset(preview, "activeBuckets", activeBuckets.join(","));
}

function isLayerSequencePreviewVisible(preview, listRect) {
  if (!(preview instanceof HTMLElement) || preview.hidden || !preview.getClientRects().length) {
    return false;
  }
  const rect = preview.getBoundingClientRect();
  return (
    rect.width > 0 &&
    rect.height > 0 &&
    rect.right > listRect.left &&
    rect.left < listRect.right &&
    rect.bottom > listRect.top &&
    rect.top < listRect.bottom
  );
}

function renderLayerSequencePreviews(now = performance.now(), options = {}) {
  if (
    !editLayerList ||
    state.sidebarTab !== "edit" ||
    state.sidebarCollapsed ||
    document.visibilityState === "hidden"
  ) {
    return;
  }
  const frameTime = Number.isFinite(Number(now)) ? Number(now) : performance.now();
  const force = options.force === true;
  const paintInterval = layerSequencePreviewReducedMotionQuery?.matches
    ? 100
    : LAYER_SEQUENCE_PREVIEW_FRAME_INTERVAL_MS;
  const lastPaintTime = Number(state.sequencePreviewLastPaintTime);
  if (!force && Number.isFinite(lastPaintTime) && frameTime - lastPaintTime < paintInterval) {
    return;
  }
  const previews = editLayerList.querySelectorAll(".edit-layer-sequence-preview");
  const rawListRect = editLayerList.getBoundingClientRect();
  const listRect = {
    left: Math.max(0, rawListRect.left),
    top: Math.max(0, rawListRect.top),
    right: Math.min(window.innerWidth, rawListRect.right),
    bottom: Math.min(window.innerHeight, rawListRect.bottom)
  };
  let paintedAny = false;
  for (const preview of previews) {
    if (!isLayerSequencePreviewVisible(preview, listRect)) {
      continue;
    }
    const stroke = getStrokeById(preview.dataset.strokeId);
    if (!stroke) {
      continue;
    }
    paintLayerSequencePreview(
      preview,
      stroke,
      Number(preview.dataset.sequenceSlotIndex) || 0,
      frameTime
    );
    paintedAny = true;
  }
  if (paintedAny) {
    state.sequencePreviewLastPaintTime = frameTime;
  }
}

function createLayerSequenceSettings(stroke, slotIndex = 0) {
  const effect = getLayerSequenceEffect(stroke, slotIndex);
  const timingStyle = getLayerSequenceTimingStyle(stroke, slotIndex);
  const settings = getLayerSequenceSettings(stroke, slotIndex);
  const panel = document.createElement("div");
  panel.className = "edit-layer-sequence-settings";
  panel.dataset.strokeId = String(stroke.id);
  panel.dataset.sequenceSlotIndex = String(slotIndex);
  panel.appendChild(createLayerSequencePreview(stroke, slotIndex));

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
  } else if (effect === "pixelate") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "pixelateAmount", "amount", 0, 64, 1, "px", slotIndex)
    );
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "pixelateSpeed", "speed", 1, 100, 1, "", slotIndex)
    );
  } else if (effect === "blur") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "blurAmount", "amount", 0, 64, 1, "px", slotIndex)
    );
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "blurSpeed", "speed", 1, 100, 1, "", slotIndex)
    );
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
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "stepRate", "step rate", 50, 4000, 50, "ms", slotIndex)
    );
  } else if (timingStyle === "random") {
    panel.appendChild(
      createLayerSequenceRangeControl(stroke, "randomSpeed", "randomization speed", 1, 100, 1, "", slotIndex)
    );
  }

  return panel;
}

function createLayerSequenceAddRemoveRow(stroke, slotIndex, slotCount) {
  const noEffects = slotCount <= 0;
  const canAdd = (noEffects || slotIndex === slotCount - 1) && slotCount < MAX_LAYER_SEQUENCE_EFFECTS;
  const canRemove = slotCount > 0;
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
    const symbol = document.createElement("span");
    symbol.className = "edit-layer-sequence-add-symbol";
    symbol.textContent = "+";
    addButton.appendChild(symbol);
    if (noEffects) {
      const label = document.createElement("span");
      label.className = "edit-layer-sequence-add-label";
      label.textContent = "add sequence effect";
      addButton.appendChild(label);
    }
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

function addLayerSequenceSlot(stroke) {
  if (!stroke) {
    return false;
  }
  const slotCount = getLayerSequenceSlotCount(stroke);
  if (slotCount >= MAX_LAYER_SEQUENCE_EFFECTS) {
    return false;
  }
  if (slotCount <= 0) {
    stroke.sequenceConfigured = true;
    stroke.sequenceEnabled = true;
    stroke.sequenceUserDisabled = false;
    stroke.sequenceEffect = "show-hide";
    stroke.sequenceTimingStyle = "pulse";
    stroke.sequenceSettings = normalizeLayerSequenceSettings(LAYER_SEQUENCE_DEFAULT_SETTINGS);
    setExtraLayerSequenceSlots(stroke, []);
    return true;
  }
  const extras = getExtraLayerSequenceSlots(stroke);
  extras.push(normalizeLayerSequenceSlot({
    effect: "show-hide",
    timingStyle: "pulse",
    settings: LAYER_SEQUENCE_DEFAULT_SETTINGS
  }));
  setExtraLayerSequenceSlots(stroke, extras);
  stroke.sequenceConfigured = true;
  stroke.sequenceEnabled = true;
  stroke.sequenceUserDisabled = false;
  return true;
}

function removeLayerSequenceSlot(stroke, slotIndex) {
  if (!stroke) {
    return false;
  }
  const slotCount = getLayerSequenceSlotCount(stroke);
  if (slotCount <= 0) {
    return false;
  }
  const safeSlotIndex = clamp(Math.floor(Number(slotIndex)) || 0, 0, slotCount - 1);
  const extras = getExtraLayerSequenceSlots(stroke);
  if (safeSlotIndex <= 0) {
    const nextSlot = extras.shift();
    if (nextSlot) {
      stroke.sequenceConfigured = true;
      stroke.sequenceEffect = nextSlot.effect;
      stroke.sequenceTimingStyle = nextSlot.timingStyle;
      stroke.sequenceSettings = normalizeLayerSequenceSettings(nextSlot.settings);
      setExtraLayerSequenceSlots(stroke, extras);
      stroke.sequenceEnabled = true;
      stroke.sequenceUserDisabled = false;
    } else {
      stroke.sequenceConfigured = false;
      stroke.sequenceEnabled = false;
      stroke.sequenceUserDisabled = false;
      setExtraLayerSequenceSlots(stroke, []);
    }
    return true;
  }
  extras.splice(safeSlotIndex - 1, 1);
  setExtraLayerSequenceSlots(stroke, extras);
  return true;
}

const strokeSerializationCache = new WeakMap();

function markStrokeSerializationDirty(stroke) {
  if (!stroke || typeof stroke !== "object") {
    return;
  }
  stroke.serializationRevision = (Number(stroke.serializationRevision) || 0) + 1;
  strokeSerializationCache.delete(stroke);
  strokeLayerBoundsCache.delete(stroke);
}

function createSerializedStroke(stroke) {
  return {
    id: Number.isFinite(Number(stroke.id)) ? Number(stroke.id) : null,
    layerNumber: Number.isFinite(Number(stroke.layerNumber)) ? Number(stroke.layerNumber) : null,
    layerType: normalizeStrokeLayerType(stroke.layerType),
    customName: normalizeLayerCustomName(stroke.customName),
    brushCategoryName: typeof stroke.brushCategoryName === "string"
      ? stroke.brushCategoryName
      : "",
    blendMode: getLayerBlendMode(stroke),
    layerOpacity: getLayerOpacityPercent(stroke),
    layerScale: getLayerScaleValue(stroke),
    layerRotation: getLayerRotationDegrees(stroke),
    hidden: Boolean(stroke.hidden),
    animationPaused: Boolean(stroke.animationPaused),
    sequenceOpen: Boolean(stroke.sequenceOpen),
    sequenceConfigured: hasLayerSequenceEffectSlots(stroke),
    sequenceEnabled: isLayerSequenceEnabled(stroke),
    sequenceUserDisabled: Boolean(stroke.sequenceUserDisabled),
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
      imageRendering:
        (element.dataset.sequenceBaseImageRendering || element.style.imageRendering) === "auto"
          ? "auto"
          : "pixelated",
      tintColor: normalizeHexColor(element.dataset.tintColor, "#ffffff"),
      tintAmount: clamp(Number(element.dataset.tintAmount) || 0, 0, 100)
    }))
  };
}

function createStrokeBrushSourceDescriptors(stroke) {
  const descriptors = new Map();
  for (const element of stroke?.elements || []) {
    const brushId = Number(element.dataset.brushId);
    const brushUrl = element.dataset.brushUrl || element.dataset.sequenceBaseSrc || "";
    if (!Number.isFinite(brushId) || !brushUrl || descriptors.has(brushId)) {
      continue;
    }
    descriptors.set(brushId, {
      id: brushId,
      url: brushUrl,
      name: `brush-${brushId}`,
      width: Math.max(1, parseFloat(element.style.width) || 1),
      height: Math.max(1, parseFloat(element.style.height) || 1)
    });
  }
  return Array.from(descriptors.values());
}

function getStrokeSerializationEntry(stroke) {
  const revision = Number(stroke?.serializationRevision) || 0;
  const cached = strokeSerializationCache.get(stroke);
  if (cached && cached.revision === revision) {
    return cached;
  }
  const entry = {
    revision,
    snapshot: createSerializedStroke(stroke),
    brushSources: createStrokeBrushSourceDescriptors(stroke)
  };
  strokeSerializationCache.set(stroke, entry);
  return entry;
}

function serializeStrokeList(strokes) {
  return strokes.map((stroke) => getStrokeSerializationEntry(stroke).snapshot);
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
      for (const descriptor of getStrokeSerializationEntry(stroke).brushSources) {
        const brushId = Number(descriptor.id);
        if (!Number.isFinite(brushId) || currentBrushIds.has(brushId)) {
          continue;
        }

        if (byId.has(brushId)) {
          continue;
        }

        const brushUrl = descriptor.url;
        if (!brushUrl) {
          continue;
        }

        byId.set(brushId, {
          id: brushId,
          url: brushUrl,
          name: descriptor.name,
          width: descriptor.width,
          height: descriptor.height
        });
      }
    }
  }

  return Array.from(byId.values());
}

function buildSessionSnapshotBase() {
  return {
    version: 1,
    stockBrushAssetRevision: STOCK_BRUSH_ASSET_REVISION,
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
    activeStockBrushFolderIds: Array.from(getActiveStockBrushFolderIdSet()),
    browsingAllStockBrushes: state.browsingAllStockBrushes,
    camera: {
      x: state.camera.x,
      y: state.camera.y,
      scale: state.camera.scale
    },
    controls: {
      size: parseNumericInputValue(sizeSlider, 100),
      consistent: consistentToggle.checked,
      consistentSize: parseNumericInputValue(consistentSizeSlider, 96),
      randomSizeEnabled: isRandomSizeEnabled(),
      randomSizePercentMin: Math.round(getRandomSizeRangeForMode(false).min),
      randomSizePercentMax: Math.round(getRandomSizeRangeForMode(false).max),
      randomSizeFixedMin: Math.round(getRandomSizeRangeForMode(true).min),
      randomSizeFixedMax: Math.round(getRandomSizeRangeForMode(true).max),
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
      brushGallerySearch: normalizeBrushGallerySearch(state.brushGallerySearch),
      brushGalleryRandomSeed: state.brushGalleryRandomSeed,
      brushGalleryPage: normalizeBrushGalleryPage(state.brushGalleryPage),
      customBrushPresetSources: getCustomBrushPresetSourcesSnapshot(),
      activeCustomBrushPresetIndex: normalizeCustomBrushPresetIndex(state.activeCustomBrushPresetIndex),
      canvasBackgroundColor: normalizeHexColor(state.canvasBackgroundColor, "#ffffff"),
      exportBackgroundEnabled: state.exportBackgroundEnabled !== false,
      exportSeeBeyondEnabled: state.exportSeeBeyondEnabled !== false,
      exportGuidelinesEnabled: Boolean(state.exportGuidelinesEnabled),
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
      exportSequencePrewarmSeconds: clamp(Number(state.exportSequencePrewarmSeconds) || 0, 0, 300),
      exportGifSizeLimitEnabled: Boolean(state.exportGifSizeLimitEnabled),
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
      durationMs: Math.max(0, Math.round(Number(brush.durationMs) || 0)),
      animated: brush.animated === true,
      opaque: brush.opaque === true,
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
      tags: getBrushTags(brush),
      stockAssetRevision:
        typeof brush.stockAssetRevision === "string" ? brush.stockAssetRevision : "",
      enabled: brush.enabled,
      weightMode: normalizeBrushWeightMode(brush.weightMode)
    }))
  };
}

function buildSessionSnapshot() {
  const redoDrawStrokes = getRedoDrawStrokes();
  return {
    ...buildSessionSnapshotBase(),
    strokeBrushes: collectStrokeBrushSources(),
    strokes: serializeStrokeList(state.strokes),
    redoStrokes: serializeStrokeList(redoDrawStrokes)
  };
}

function getSessionStrokeToken(stroke) {
  if (!stroke || typeof stroke !== "object") {
    return "";
  }
  let token = sessionStrokeTokenByObject.get(stroke);
  if (!token) {
    token = `stroke-${nextSessionStrokeToken++}`;
    sessionStrokeTokenByObject.set(stroke, token);
  }
  return token;
}

function buildSessionSerializePatch() {
  const currentStrokes = state.strokes.slice();
  const redoStrokes = getRedoDrawStrokes();
  const strokeOrder = currentStrokes.map(getSessionStrokeToken);
  const redoStrokeOrder = redoStrokes.map(getSessionStrokeToken);
  const activeTokens = new Set([...strokeOrder, ...redoStrokeOrder]);
  const updateRevisions = new Map();
  const updates = [];
  const seenTokens = new Set();

  for (const stroke of [...currentStrokes, ...redoStrokes]) {
    const token = getSessionStrokeToken(stroke);
    if (!token || seenTokens.has(token)) {
      continue;
    }
    seenTokens.add(token);
    const entry = getStrokeSerializationEntry(stroke);
    const acknowledged = sessionSerializerAcknowledgedRevisions.get(token);
    if (acknowledged === entry.revision) {
      continue;
    }
    updates.push({
      token,
      revision: entry.revision,
      snapshot: entry.snapshot,
      brushSources: entry.brushSources
    });
    updateRevisions.set(token, entry.revision);
  }

  return {
    base: buildSessionSnapshotBase(),
    strokeOrder,
    redoStrokeOrder,
    updates,
    updateRevisions,
    activeTokens,
    stampCount: currentStrokes.reduce(
      (total, stroke) => total + (Array.isArray(stroke?.elements) ? stroke.elements.length : 0),
      0
    )
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
  const frameTimeMs = SAVED_PREVIEW_FRAME_TIME_MS;
  const bounds = fitBoundsToAspect(
    computeInitialExportSelectionBounds(),
    outputWidth / outputHeight
  );
  const entries = await collectExportStampEntries(bounds);
  const blob = await renderExportPngBlob(
    bounds,
    outputWidth,
    outputHeight,
    entries,
    {
      includeBackground: true,
      backgroundColor: state.canvasBackgroundColor,
      frameTimeMs,
      singleGifFrameTimeMs: frameTimeMs,
      releaseSourceImagesAfterRender: true
    }
  );
  return readBlobAsDataUrl(blob);
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
    const snapshotSaveRevision = state.saveRevision;
    const snapshot = buildSessionSnapshot();
    const snapshotJson = JSON.stringify(snapshot);
    const savedAt = Date.now();
    const id = `${savedAt}-${Math.random().toString(36).slice(2, 8)}`;
    const currentIndex = state.savedCompositionsLoaded
      ? state.savedCompositions
      : await getSavedCompositionIndex();
    let thumbnailUrl = "";
    let thumbnailError = null;
    try {
      thumbnailUrl = await createSavedCompositionThumbnail();
      if (state.saveRevision !== snapshotSaveRevision) {
        const error = new Error("The scene changed while its saved preview was rendering.");
        error.code = "SAVED_PREVIEW_STALE";
        throw error;
      }
    } catch (error) {
      thumbnailUrl = "";
      thumbnailError = error;
      console.error("Could not create saved composition preview.", error);
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
    setSavedCompositionsStatus(thumbnailError ? "saved (preview unavailable)" : "saved");
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
    state.saveEpoch += 1;
    cancelScheduledSessionSave(true);
    state.savedRevision = state.saveRevision;
    const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    try {
      sessionStorage.setItem(SESSION_STORAGE_KEY, snapshotJson);
      removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
      removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
      cleanupSupersededLifecycleSnapshot(previousPointer);
    } catch (error) {
      removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
      setSessionStorageItemSafe(
        SESSION_STORAGE_POINTER_KEY,
        `${SESSION_IDB_PREFIX}${SAVED_COMPOSITION_KEY_PREFIX}${id}`
      );
      removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
      cleanupSupersededLifecycleSnapshot(previousPointer);
    }
    await yieldToMainThread();
    const restored = await restoreSessionState(snapshotJson);
    if (!restored) {
      setSavedCompositionsStatus("could not load");
      return;
    }
    refreshLayerSequenceLoop();
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

function disposeSessionSerializerWorker(error = null) {
  if (sessionSerializerWorker) {
    sessionSerializerWorker.terminate();
    sessionSerializerWorker = null;
  }
  sessionSerializerAcknowledgedRevisions.clear();
  if (error) {
    for (const request of sessionSerializerRequests.values()) {
      request.reject(error);
    }
  }
  sessionSerializerRequests.clear();
}

function getSessionSerializerWorker() {
  if (sessionSerializerWorker || typeof Worker !== "function") {
    return sessionSerializerWorker;
  }
  try {
    const worker = new Worker(SESSION_SERIALIZE_WORKER_URL);
    worker.addEventListener("message", (event) => {
      const requestId = Number(event.data?.requestId);
      const request = sessionSerializerRequests.get(requestId);
      if (!request) {
        return;
      }
      sessionSerializerRequests.delete(requestId);
      if (event.data?.type === "serialized" && typeof event.data.json === "string") {
        for (const [token, revision] of request.updateRevisions || []) {
          sessionSerializerAcknowledgedRevisions.set(token, revision);
        }
        for (const token of Array.from(sessionSerializerAcknowledgedRevisions.keys())) {
          if (!request.activeTokens?.has(token)) {
            sessionSerializerAcknowledgedRevisions.delete(token);
          }
        }
        request.resolve(event.data.json);
      } else {
        request.reject(new Error(event.data?.message || "Session serialization failed."));
      }
    });
    worker.addEventListener("error", () => {
      disposeSessionSerializerWorker(new Error("Session serialization worker failed."));
    });
    sessionSerializerWorker = worker;
  } catch (error) {
    sessionSerializerWorker = null;
  }
  return sessionSerializerWorker;
}

async function serializeSessionStateIncrementally() {
  const worker = getSessionSerializerWorker();
  if (!worker) {
    const snapshot = buildSessionSnapshot();
    return {
      json: JSON.stringify(snapshot),
      stampCount: getSnapshotStampCount(snapshot)
    };
  }
  const patch = buildSessionSerializePatch();
  const requestId = ++sessionSerializerRequestId;
  try {
    const json = await new Promise((resolve, reject) => {
      sessionSerializerRequests.set(requestId, {
        resolve,
        reject,
        updateRevisions: patch.updateRevisions,
        activeTokens: patch.activeTokens
      });
      try {
        worker.postMessage({
          type: "serialize-incremental",
          requestId,
          base: patch.base,
          strokeOrder: patch.strokeOrder,
          redoStrokeOrder: patch.redoStrokeOrder,
          updates: patch.updates
        });
      } catch (error) {
        sessionSerializerRequests.delete(requestId);
        reject(error);
      }
    });
    return { json, stampCount: patch.stampCount };
  } catch (error) {
    disposeSessionSerializerWorker();
    const snapshot = buildSessionSnapshot();
    return {
      json: JSON.stringify(snapshot),
      stampCount: getSnapshotStampCount(snapshot)
    };
  }
}

async function persistSessionSnapshotJson(snapshotJson, stampCount, epoch, revision) {
  const tabId = getSessionTabId();
  const canCommitSnapshot = () =>
    epoch === state.saveEpoch &&
    (!Number.isFinite(Number(revision)) || Number(revision) >= state.savedRevision) &&
    !(getSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY) || "")
      .startsWith(SESSION_IDB_PREFIX);
  const shouldUseIndexedDb =
    Math.max(0, Number(stampCount) || 0) >= SAVE_DIRECT_IDB_STAMP_THRESHOLD ||
    snapshotJson.length >= 1_000_000;

  if (!shouldUseIndexedDb) {
    try {
      if (!canCommitSnapshot()) {
        return false;
      }
      const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
      sessionStorage.setItem(SESSION_STORAGE_KEY, snapshotJson);
      removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
      removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
      cleanupSupersededLifecycleSnapshot(previousPointer);
      return true;
    } catch (error) {
      // Large snapshots and restrictive storage modes fall through to IndexedDB.
    }
  }

  try {
    await writeSnapshotToIndexedDb(tabId, snapshotJson);
    if (!canCommitSnapshot()) {
      return false;
    }
    const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
    setSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY, `${SESSION_IDB_PREFIX}${tabId}`);
    removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
    cleanupSupersededLifecycleSnapshot(previousPointer, tabId);
    return true;
  } catch (error) {
    if (shouldUseIndexedDb && canCommitSnapshot()) {
      try {
        const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
        sessionStorage.setItem(SESSION_STORAGE_KEY, snapshotJson);
        removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
        removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
        cleanupSupersededLifecycleSnapshot(previousPointer);
        return true;
      } catch (secondaryError) {
        // Ignore transient quota/storage issues and continue app runtime.
      }
    }
  }
  return false;
}

async function saveSessionStateNow() {
  if (state.saveInFlight) {
    return;
  }
  const revision = state.saveRevision;
  const epoch = state.saveEpoch;
  state.saveUrgentPending = false;
  state.saveInFlight = true;
  try {
    const serialized = await serializeSessionStateIncrementally();
    if (epoch !== state.saveEpoch) {
      return;
    }
    const persisted = await persistSessionSnapshotJson(
      serialized.json,
      serialized.stampCount,
      epoch,
      revision
    );
    if (persisted && epoch === state.saveEpoch) {
      state.savedRevision = Math.max(state.savedRevision, revision);
      state.saveFailureCount = 0;
    } else if (epoch === state.saveEpoch) {
      state.saveFailureCount = Math.min(8, state.saveFailureCount + 1);
    }
  } finally {
    state.saveInFlight = false;
    if (state.savedRevision < state.saveRevision) {
      if (state.saveUrgentPending && state.saveFailureCount === 0) {
        queueUrgentSessionSave();
      } else {
        queueSessionSave();
      }
    }
  }
}

function cancelDeferredSessionSave() {
  if (state.saveTimerId !== null) {
    window.clearTimeout(state.saveTimerId);
    state.saveTimerId = null;
  }
  if (state.saveIdleCallbackId !== null) {
    if (typeof window.cancelIdleCallback === "function") {
      window.cancelIdleCallback(state.saveIdleCallbackId);
    } else {
      window.clearTimeout(state.saveIdleCallbackId);
    }
    state.saveIdleCallbackId = null;
  }
}

function cancelUrgentSessionSaveSchedule(clearPending = false) {
  if (state.saveUrgentTimerId !== null) {
    window.clearTimeout(state.saveUrgentTimerId);
    state.saveUrgentTimerId = null;
  }
  if (clearPending) {
    state.saveUrgentPending = false;
  }
}

function cancelScheduledSessionSave(clearUrgentPending = false) {
  cancelDeferredSessionSave();
  cancelUrgentSessionSaveSchedule(clearUrgentPending);
}

function queueSessionSave() {
  if (
    state.saveTimerId !== null ||
    state.saveIdleCallbackId !== null ||
    state.saveInFlight
  ) {
    return;
  }
  const retryDelay = state.saveFailureCount > 0
    ? Math.min(30000, SAVE_DEBOUNCE_MS * 2 ** state.saveFailureCount)
    : SAVE_DEBOUNCE_MS;
  state.saveTimerId = window.setTimeout(() => {
    state.saveTimerId = null;
    const runSave = () => {
      state.saveIdleCallbackId = null;
      void saveSessionStateNow();
    };
    state.saveIdleCallbackId = typeof window.requestIdleCallback === "function"
      ? window.requestIdleCallback(runSave, { timeout: SAVE_IDLE_TIMEOUT_MS })
      : window.setTimeout(runSave, 0);
  }, retryDelay);
}

function queueUrgentSessionSave() {
  state.saveUrgentPending = true;
  if (
    state.saveInFlight ||
    state.saveUrgentMicrotaskQueued ||
    state.saveUrgentTimerId !== null
  ) {
    return;
  }
  cancelDeferredSessionSave();
  const now = performance.now();
  const lastStartedAt = Number(state.saveUrgentLastStartedAt);
  const elapsed = Number.isFinite(lastStartedAt) ? now - lastStartedAt : Infinity;
  const throttleDelay = Math.max(0, SAVE_URGENT_MIN_INTERVAL_MS - elapsed);
  if (throttleDelay > 0) {
    state.saveUrgentTimerId = window.setTimeout(() => {
      state.saveUrgentTimerId = null;
      if (state.saveUrgentPending) {
        queueUrgentSessionSave();
      }
    }, throttleDelay);
    return;
  }
  state.saveUrgentMicrotaskQueued = true;
  window.queueMicrotask(() => {
    state.saveUrgentMicrotaskQueued = false;
    if (!state.saveUrgentPending || state.saveInFlight) {
      return;
    }
    state.saveUrgentPending = false;
    state.saveUrgentLastStartedAt = performance.now();
    void saveSessionStateNow();
  });
}

function scheduleSessionSave() {
  state.saveRevision += 1;
  if (state.stampCount >= SAVE_DIRECT_IDB_STAMP_THRESHOLD && state.saveFailureCount === 0) {
    queueUrgentSessionSave();
  } else {
    cancelUrgentSessionSaveSchedule(true);
    queueSessionSave();
  }
}

function saveSessionStateSynchronously(snapshotJson = null, revision = state.saveRevision) {
  try {
    const serialized = typeof snapshotJson === "string"
      ? snapshotJson
      : JSON.stringify(buildSessionSnapshot());
    const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    sessionStorage.setItem(SESSION_STORAGE_KEY, serialized);
    removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
    cleanupSupersededLifecycleSnapshot(previousPointer);
    state.savedRevision = Math.max(state.savedRevision, Number(revision) || 0);
    state.saveFailureCount = 0;
    return true;
  } catch (error) {
    return false;
  }
}

function persistLifecycleSessionSnapshot(snapshotJson, revision) {
  const tabId = getSessionTabId();
  const lifecycleKey = `${tabId}:lifecycle:${Number(revision) || 0}:${Date.now()}`;
  const lifecyclePointer = `${SESSION_IDB_PREFIX}${lifecycleKey}`;
  if (!setSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY, lifecyclePointer)) {
    return false;
  }

  const writePromise = snapshotDbConnection
    ? beginSnapshotWriteToIndexedDb(snapshotDbConnection, lifecycleKey, snapshotJson)
    : writeSnapshotToIndexedDb(lifecycleKey, snapshotJson);
  void writePromise.then(() => {
    if (getSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY) !== lifecyclePointer) {
      return;
    }
    if (state.saveRevision !== revision) {
      removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
      cleanupSupersededLifecycleSnapshot(
        lifecyclePointer,
        getLifecycleSnapshotKeyFromPointer(
          getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY)
        )
      );
      return;
    }
    const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    if (setSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY, lifecyclePointer)) {
      removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
      removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
      cleanupSupersededLifecycleSnapshot(previousPointer, lifecycleKey);
    }
    state.savedRevision = Math.max(state.savedRevision, revision);
    state.saveFailureCount = 0;
  }).catch(() => {
    if (getSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY) === lifecyclePointer) {
      removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
    }
    if (lastLifecycleFlushRevision === revision) {
      lastLifecycleFlushRevision = -1;
    }
    state.saveFailureCount = Math.min(8, state.saveFailureCount + 1);
  });
  return true;
}

function flushSessionSaveNow(event = null) {
  const isLifecycleFlush = event?.type === "pagehide" || event?.type === "beforeunload";
  if (isLifecycleFlush) {
    const revision = state.saveRevision;
    if (lastLifecycleFlushRevision === revision) {
      return;
    }
    lastLifecycleFlushRevision = revision;
    cancelScheduledSessionSave(true);
    let snapshotJson;
    try {
      snapshotJson = JSON.stringify(buildSessionSnapshot());
    } catch (error) {
      lastLifecycleFlushRevision = -1;
      return;
    }
    if (!saveSessionStateSynchronously(snapshotJson, revision)) {
      if (!persistLifecycleSessionSnapshot(snapshotJson, revision)) {
        lastLifecycleFlushRevision = -1;
      }
    }
    return;
  }
  state.saveRevision += 1;
  cancelScheduledSessionSave(true);
  // If another save is already serializing, preserve an immediate trailing
  // flush instead of letting a hidden-page idle callback carry the update.
  state.saveUrgentPending = true;
  state.saveUrgentLastStartedAt = -Infinity;
  void saveSessionStateNow();
}

function createStampElement(stampData, brush, fallbackTintSettings = null, deferSource = false) {
  const width = Math.max(1, Number(stampData.width) || brush.width);
  const height = Math.max(1, Number(stampData.height) || brush.height);
  const stamp = document.createElement("img");

  stamp.className = "stamp";
  stamp.alt = "";
  stamp.draggable = false;
  stamp.loading = "lazy";
  stamp.decoding = "async";
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
  stamp.dataset.sequenceBaseOpacity = stamp.style.opacity;
  stamp.dataset.sequenceBaseSrc = brush.url;
  stamp.dataset.sequenceDisplayedSource = brush.url;
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

  const initialBounds = getStampWorldBoundsFromLayout(
    Number(stampData.left) || 0,
    Number(stampData.top) || 0,
    width,
    height,
    rotation
  );
  const shouldDeferSource =
    deferSource ||
    !rectsIntersect(initialBounds, getViewportWorldBounds(STAMP_VIEWPORT_CULL_MARGIN_PX));
  if (shouldDeferSource) {
    stamp.dataset.viewportCulled = "true";
    stamp.classList.add("is-culled");
    stamp.src = TRANSPARENT_STAMP_SRC;
  } else {
    stamp.src = brush.url;
    markGifPlaybackStart(stamp, brush.url);
    applyGifPauseStateToImage(stamp);
  }

  return stamp;
}

function resolveBrushForStamp(stampData, brushById) {
  const brushId = Number(stampData?.brushId);
  let brush = Number.isFinite(brushId) ? brushById.get(brushId) : null;
  if (!brush && typeof stampData?.url === "string") {
    const source = getCanonicalStockBrushSource(stampData.url);
    brush =
      state.brushes.find(
        (entry) =>
          getBrushPrimarySourceUrl(entry) === source ||
          normalizeFavoriteBrushSource(entry.url) === normalizeFavoriteBrushSource(stampData.url)
      ) || null;
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
    const sequenceEffect = normalizeLayerSequenceValue(
      strokeData?.sequenceEffect || strokeData?.sequenceEffects,
      LAYER_SEQUENCE_EFFECT_OPTIONS
    );
    const stroke = {
      id: strokeId,
      layerNumber: Number.isFinite(Number(strokeData?.layerNumber))
        ? Number(strokeData.layerNumber)
        : strokeId,
      layerType: normalizeStrokeLayerType(strokeData?.layerType),
      customName: normalizeLayerCustomName(strokeData?.customName),
	      brushCategoryName:
	        typeof strokeData?.brushCategoryName === "string" && strokeData.brushCategoryName.trim()
	          ? strokeData.brushCategoryName.trim()
	          : "custom",
	      blendMode: normalizeLayerBlendMode(strokeData?.blendMode),
	      layerOpacity: Number.isFinite(Number(strokeData?.layerOpacity))
	        ? normalizeLayerOpacityPercent(strokeData.layerOpacity, 100)
	        : null,
	      layerScale: normalizeLayerScaleValue(strokeData?.layerScale),
	      layerRotation: normalizeLayerRotationDegrees(strokeData?.layerRotation),
	      hidden: Boolean(strokeData?.hidden),
	      animationPaused: Boolean(strokeData?.animationPaused),
	      sequenceOpen: Boolean(strokeData?.sequenceOpen),
	      sequenceConfigured:
	        typeof strokeData?.sequenceConfigured === "boolean"
	          ? strokeData.sequenceConfigured
	          : Boolean(strokeData?.sequenceEnabled || strokeData?.sequenceOpen) ||
	            normalizeExtraLayerSequenceSlots(strokeData?.sequenceEffectSlots).length > 0,
	      sequenceEnabled:
	        typeof strokeData?.sequenceEnabled === "boolean"
	          ? strokeData.sequenceEnabled
	          : Boolean(strokeData?.sequenceOpen),
	      sequenceUserDisabled: Boolean(strokeData?.sequenceUserDisabled),
	      sequenceEffect,
	      sequenceTimingStyle: normalizeLayerSequenceTimingStyle(
	        strokeData?.sequenceTimingStyle || strokeData?.sequenceTimingStyles,
	        sequenceEffect
	      ),
	      sequenceSettings: normalizeLayerSequenceSettings(strokeData?.sequenceSettings),
	      sequenceEffectSlots: normalizeExtraLayerSequenceSlots(strokeData?.sequenceEffectSlots),
	      elements: []
	    };
    if (stroke.sequenceConfigured && !stroke.sequenceUserDisabled) {
      stroke.sequenceEnabled = true;
    }
    if (strokeId >= state.nextStrokeId) {
      state.nextStrokeId = strokeId + 1;
    }
    const stamps = Array.isArray(strokeData?.stamps) ? strokeData.stamps : [];
    for (const stampData of stamps) {
      const brush = resolveBrushForStamp(stampData, brushById);
      if (!brush) {
        continue;
      }

      const stamp = createStampElement(
        stampData,
        brush,
        fallbackTintSettings,
        !appendToWorld
      );
      stamp.dataset.strokeId = String(stroke.id);
      if (appendToWorld) {
        fragment.appendChild(stamp);
        state.stampCount += 1;
        cacheStampWorldBounds(stamp);
        incrementUrlRef(brush.url);
        restoredStampRefs.push({ stamp, stroke });
      }
      stroke.elements.push(stamp);
    }

    if (stroke.elements.length) {
      applyStrokeBlendMode(stroke);
      applyStrokeLayerVisuals(stroke);
      restored.push(stroke);
    }
  }

  if (appendToWorld && restoredStampRefs.length) {
    world.appendChild(fragment);
    const viewportBounds = getViewportVisibilityBounds();
    for (const { stamp, stroke } of restoredStampRefs) {
      const hidden = Boolean(stroke.hidden);
      stamp.classList.toggle("is-layer-hidden", hidden);
      if (!hidden) {
        registerStampSpatialCells(stamp);
        updateStampViewportVisibility(stamp, viewportBounds);
      }
    }
    scheduleStampVisibilityRefresh();
  }
  return restored;
}

async function readPendingLifecycleSessionSnapshot() {
  const pendingPointer = getSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY) || "";
  if (!pendingPointer.startsWith(SESSION_IDB_PREFIX)) {
    return null;
  }
  const pendingTabId = pendingPointer.slice(SESSION_IDB_PREFIX.length);
  let raw = null;
  if (pendingTabId) {
    for (let attempt = 0; attempt <= SESSION_PENDING_SNAPSHOT_RETRY_DELAYS_MS.length; attempt += 1) {
      if (attempt > 0) {
        await new Promise((resolve) => {
          window.setTimeout(resolve, SESSION_PENDING_SNAPSHOT_RETRY_DELAYS_MS[attempt - 1]);
        });
      }
      try {
        raw = await readSnapshotFromIndexedDb(pendingTabId);
      } catch (error) {
        raw = null;
      }
      if (raw) {
        break;
      }
    }
  }
  let keepPendingPointer = false;
  if (raw) {
    const previousPointer = getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    if (setSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY, pendingPointer)) {
      removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
      cleanupSupersededLifecycleSnapshot(previousPointer, pendingTabId);
    } else {
      keepPendingPointer = true;
    }
  } else {
    cleanupSupersededLifecycleSnapshot(
      pendingPointer,
      getLifecycleSnapshotKeyFromPointer(
        getSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY)
      )
    );
  }
  if (!keepPendingPointer) {
    removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
  }
  return raw;
}

async function restoreSessionState(rawSnapshot = null) {
  let raw = typeof rawSnapshot === "string" ? rawSnapshot : null;
  if (!raw) {
    raw = await readPendingLifecycleSessionSnapshot();
  }
  if (!raw) {
    raw = getSessionStorageItemSafe(SESSION_STORAGE_KEY);
  }
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
    const stockBrushAssetRevisionChanged =
      snapshot.stockBrushAssetRevision !== STOCK_BRUSH_ASSET_REVISION;

    const restoredBrushes = Array.isArray(snapshot.brushes) ? snapshot.brushes : [];
    state.brushes = restoredBrushes
      .filter((brush) => brush && typeof brush.url === "string" && Number.isFinite(Number(brush.id)))
      .map((brush) => {
        const originalUrl = getCanonicalStockBrushSource(
          typeof brush.originalUrl === "string" && brush.originalUrl
            ? brush.originalUrl
            : brush.url
        );
        const restoredBrush = {
          id: Number(brush.id),
          url: resolveRestoredBrushUrl(brush.url, originalUrl),
          name: String(brush.name || "brush"),
          width: Math.max(1, Number(brush.width) || 1),
          height: Math.max(1, Number(brush.height) || 1),
          originalUrl,
          originalWidth: Math.max(1, Number(brush.originalWidth) || Number(brush.width) || 1),
          originalHeight: Math.max(1, Number(brush.originalHeight) || Number(brush.height) || 1),
          frameCount:
            normalizeBrushFrameCount(brush.frameCount) ||
            (getBrushSourceIsGif(brush) ? null : 1),
          durationMs: Math.max(0, Math.round(Number(brush.durationMs) || 0)),
          animated: brush.animated === true,
          opaque: brush.opaque === true,
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
          tags: normalizeBrushTags(brush.tags),
          stockAssetRevision:
            typeof brush.stockAssetRevision === "string" ? brush.stockAssetRevision : "",
          enabled: brush.enabled !== false,
          weightMode: normalizeBrushWeightMode(brush.weightMode)
        };
        const stockMetadata = getStockBrushMetadataForSource(restoredBrush.originalUrl);
        if (stockMetadata) {
          restoredBrush.name = stockMetadata.name;
          restoredBrush.frameCount = stockMetadata.frameCount || restoredBrush.frameCount;
          restoredBrush.durationMs = stockMetadata.durationMs;
          restoredBrush.animated = stockMetadata.animated;
          restoredBrush.opaque = stockMetadata.opaque;
        }
        restoredBrush.tags = getBrushTags(restoredBrush);
        return restoredBrush;
      });
    clearBrushFrameCountJobs();
    const refreshedStockBrushCount = await refreshRestoredStockBrushes(state.brushes);

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
    const snapshotStockFolderIds = Array.isArray(snapshot.activeStockBrushFolderIds)
      ? snapshot.activeStockBrushFolderIds
      : [];
    if (snapshotStockFolderId === "all") {
      setActiveStockBrushFolders(
        getOrderedStockBrushFolders()
          .filter((folder) => getStockBrushFiles(folder).length)
          .map((folder) => folder.id),
        "all"
      );
    } else if (snapshotStockFolderIds.length) {
      setActiveStockBrushFolders(snapshotStockFolderIds);
    } else if (snapshotStockFolderId === "favorites") {
      clearActiveStockBrushFolders();
      state.activeStockBrushFolderId = "favorites";
    } else if (getStockBrushFolderById(snapshotStockFolderId)) {
      setActiveStockBrushFolders([snapshotStockFolderId], "single");
    } else {
      clearActiveStockBrushFolders();
    }
    state.browsingAllStockBrushes = Boolean(snapshot.browsingAllStockBrushes);
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

    if (sceneRendererWorker || state.sceneRendererActive || state.sceneRendererPreparing) {
      deactivateSceneRenderer({ dispose: true });
    }
    sceneRendererUnsupportedSources.clear();
    world.innerHTML = "";
    if (exportBgImageLayer) {
      world.appendChild(exportBgImageLayer);
    }
    state.viewportRenderedStamps.clear();
    state.occlusionCulledStamps.clear();
    cancelStampOcclusionRefresh();
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
      const sourceUrl =
        typeof source?.url === "string"
          ? resolveRestoredBrushUrl(source.url, source.url)
          : "";
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
    resetKeyboardHistoryTracking();
    state.history = state.strokes.map((stroke) => ({ type: "draw", stroke }));
    state.redoHistory = restoredRedoStrokes.map((stroke) => ({ type: "draw", stroke }));
    for (const action of state.history) {
      markKeyboardHistoryActionPerformed(action);
    }
    for (const action of state.redoHistory) {
      markKeyboardHistoryActionUndone(action);
    }

    setInputNumericValue(sizeSlider, controls.size);
    consistentToggle.checked = Boolean(controls.consistent);
    setInputNumericValue(consistentSizeSlider, controls.consistentSize);
    state.randomSizeEnabled = Boolean(controls.randomSizeEnabled);
    if (randomSizeToggle) {
      randomSizeToggle.checked = state.randomSizeEnabled;
    }
    setRandomSizeRangeForMode(controls.randomSizePercentMin, controls.randomSizePercentMax, false);
    setRandomSizeRangeForMode(controls.randomSizeFixedMin, controls.randomSizeFixedMax, true);
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
    state.brushGallerySort = DEFAULT_BRUSH_GALLERY_SORT;
    state.brushGallerySearch = normalizeBrushGallerySearch(controls.brushGallerySearch);
    state.brushGalleryRandomSeed =
      normalizeBrushGalleryRandomSeed(controls.brushGalleryRandomSeed) ?? createBrushGalleryRandomSeed();
    state.brushGalleryPage = 0;
    state.exportBackgroundEnabled = controls.exportBackgroundEnabled !== false;
    state.exportSeeBeyondEnabled = controls.exportSeeBeyondEnabled !== false;
    state.exportGuidelinesEnabled = Boolean(controls.exportGuidelinesEnabled);
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
    state.exportSequencePrewarmSeconds = Number.isFinite(Number(controls.exportSequencePrewarmSeconds))
      ? clamp(Number(controls.exportSequencePrewarmSeconds), 0, 300)
      : 0;
    state.exportGifSizeLimitEnabled = Boolean(controls.exportGifSizeLimitEnabled);
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
    if (stockBrushAssetRevisionChanged || refreshedStockBrushCount > 0) {
      scheduleSessionSave();
    }
    if (snapshot.browsingAllStockBrushes) {
      await browseAllStockBrushFolders({ preserveGalleryState: true });
    }
    scheduleSceneRendererEvaluation();
    return true;
  } catch (error) {
    removeSessionStorageItemSafe(SESSION_STORAGE_KEY);
    removeSessionStorageItemSafe(SESSION_STORAGE_POINTER_KEY);
    removeSessionStorageItemSafe(SESSION_STORAGE_PENDING_POINTER_KEY);
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

function normalizeBrushTags(value) {
  const rawTags = Array.isArray(value)
    ? value
    : value instanceof Set
    ? Array.from(value)
    : [];
  const seen = new Set();
  const tags = [];
  for (const rawTag of rawTags) {
    const tag = String(rawTag || "").trim().replace(/^#+/, "").trim();
    const key = tag.toLocaleLowerCase();
    if (!tag || seen.has(key)) {
      continue;
    }
    seen.add(key);
    tags.push(tag);
  }
  return tags;
}

function getStockBrushSourceLookupKey(source) {
  const normalizedSource = normalizeFavoriteBrushSource(source);
  if (!normalizedSource || /^(?:blob|data):/i.test(normalizedSource)) {
    return "";
  }
  try {
    const resolvedUrl = new URL(normalizedSource, document.baseURI);
    const documentUrl = new URL(document.baseURI);
    if (
      /^https?:$/i.test(resolvedUrl.protocol) &&
      resolvedUrl.origin !== documentUrl.origin
    ) {
      return `${resolvedUrl.origin}${resolvedUrl.pathname}`;
    }
    return resolvedUrl.pathname;
  } catch (error) {
    return normalizedSource.split(/[?#]/)[0];
  }
}

function getStockBrushSourceInfoMap() {
  if (stockBrushSourceInfoByLookupKey instanceof Map) {
    return stockBrushSourceInfoByLookupKey;
  }

  const sourceInfoByLookupKey = new Map();
  for (const folder of getOrderedStockBrushFolders()) {
    for (const filePath of getStockBrushFiles(folder)) {
      const canonicalSource = normalizeFavoriteBrushSource(encodeStockBrushPath(filePath));
      const sourceKey = getStockBrushSourceLookupKey(canonicalSource);
      if (!sourceKey || sourceInfoByLookupKey.has(sourceKey)) {
        continue;
      }
      sourceInfoByLookupKey.set(sourceKey, {
        canonicalSource,
        folderId: folder.id
      });
    }
  }
  for (const [legacyFilePath, currentFilePath] of STOCK_BRUSH_SOURCE_ALIASES) {
    const legacyKey = getStockBrushSourceLookupKey(encodeStockBrushPath(legacyFilePath));
    const currentKey = getStockBrushSourceLookupKey(encodeStockBrushPath(currentFilePath));
    const currentInfo = currentKey ? sourceInfoByLookupKey.get(currentKey) : null;
    if (legacyKey && currentInfo) {
      sourceInfoByLookupKey.set(legacyKey, currentInfo);
    }
  }
  stockBrushSourceInfoByLookupKey = sourceInfoByLookupKey;
  return stockBrushSourceInfoByLookupKey;
}

function getStockBrushSourceInfo(source) {
  const sourceKey = getStockBrushSourceLookupKey(source);
  return sourceKey ? getStockBrushSourceInfoMap().get(sourceKey) || null : null;
}

function getCanonicalStockBrushSource(source) {
  const normalizedSource = normalizeFavoriteBrushSource(source);
  if (!normalizedSource) {
    return "";
  }
  return getStockBrushSourceInfo(normalizedSource)?.canonicalSource || normalizedSource;
}

function getStockBrushAssetRevisionForSource(source) {
  const folderId = getStockBrushSourceInfo(source)?.folderId;
  return folderId
    ? STOCK_BRUSH_ASSET_REVISIONS_BY_FOLDER.get(folderId) || STOCK_BRUSH_ASSET_REVISION
    : "";
}

function getStockBrushRequestUrl(source) {
  const canonicalSource = getCanonicalStockBrushSource(source);
  if (!canonicalSource) {
    return "";
  }
  const revision = getStockBrushAssetRevisionForSource(canonicalSource);
  if (!revision) {
    return canonicalSource;
  }
  const separator = canonicalSource.includes("?") ? "&" : "?";
  return `${canonicalSource}${separator}brushv=${encodeURIComponent(revision)}`;
}

function resolveRestoredBrushUrl(url, originalSource = url) {
  const normalizedUrl = normalizeFavoriteBrushSource(url);
  const canonicalOriginalSource = getCanonicalStockBrushSource(originalSource);
  if (!normalizedUrl || !getStockBrushSourceInfo(canonicalOriginalSource)) {
    return normalizedUrl;
  }
  if (
    !/^(?:blob|data):/i.test(normalizedUrl) &&
    getStockBrushSourceLookupKey(getCanonicalStockBrushSource(normalizedUrl)) ===
      getStockBrushSourceLookupKey(canonicalOriginalSource)
  ) {
    return getStockBrushRequestUrl(canonicalOriginalSource);
  }
  return normalizedUrl;
}

function getStockBrushCategoryTagMap() {
  if (stockBrushCategoryTagsBySource instanceof Map) {
    return stockBrushCategoryTagsBySource;
  }

  const tagsBySource = new Map();
  for (const folder of getOrderedStockBrushFolders()) {
    const tag = String(folder?.name || folder?.id || "").trim();
    if (!tag) {
      continue;
    }
    for (const filePath of getStockBrushFiles(folder)) {
      const sourceKey = getStockBrushSourceLookupKey(encodeStockBrushPath(filePath));
      if (!sourceKey) {
        continue;
      }
      const tags = tagsBySource.get(sourceKey) || [];
      if (!tags.some((existingTag) => existingTag.toLocaleLowerCase() === tag.toLocaleLowerCase())) {
        tags.push(tag);
      }
      tagsBySource.set(sourceKey, tags);
    }
  }
  stockBrushCategoryTagsBySource = tagsBySource;
  return stockBrushCategoryTagsBySource;
}

function getStockBrushTagsForSource(source) {
  const canonicalSource = getCanonicalStockBrushSource(source);
  const metadata = getStockBrushMetadataForSource(canonicalSource);
  const sourceKey = getStockBrushSourceLookupKey(canonicalSource);
  const categoryTags = sourceKey
    ? getStockBrushCategoryTagMap().get(sourceKey) || []
    : [];
  return normalizeBrushTags([
    ...categoryTags,
    ...(metadata?.tags || [])
  ]);
}

function getStockBrushMetadataMap() {
  if (stockBrushMetadataBySource instanceof Map) {
    return stockBrushMetadataBySource;
  }

  const metadataBySource = new Map();
  for (const [filePath, rawMetadata] of Object.entries(STOCK_BRUSH_METADATA)) {
    const sourceKey = getStockBrushSourceLookupKey(encodeStockBrushPath(filePath));
    if (!sourceKey || !rawMetadata || typeof rawMetadata !== "object") {
      continue;
    }
    const name = String(rawMetadata.name || "").trim();
    const tags = normalizeBrushTags(rawMetadata.tags).filter((tag) =>
      STOCK_BRUSH_METADATA_TAGS.has(tag.toLocaleLowerCase())
    );
    const width = Math.max(0, Math.round(Number(rawMetadata.width) || 0));
    const height = Math.max(0, Math.round(Number(rawMetadata.height) || 0));
    const frameCount = normalizeBrushFrameCount(rawMetadata.frameCount);
    const durationMs = Math.max(0, Math.round(Number(rawMetadata.durationMs) || 0));
    metadataBySource.set(sourceKey, {
      name: name || getBrushSourceFileName(filePath),
      tags,
      width,
      height,
      frameCount,
      durationMs,
      animated: rawMetadata.animated === true || Boolean(frameCount && frameCount > 1),
      opaque: rawMetadata.opaque === true
    });
  }
  stockBrushMetadataBySource = metadataBySource;
  return stockBrushMetadataBySource;
}

function getStockBrushMetadataForSource(source) {
  const sourceKey = getStockBrushSourceLookupKey(getCanonicalStockBrushSource(source));
  return sourceKey ? getStockBrushMetadataMap().get(sourceKey) || null : null;
}

function getBrushTags(brush) {
  const source = brush?.originalUrl || brush?.url || "";
  const metadata = getStockBrushMetadataForSource(source);
  const stockSourceInfo = getStockBrushSourceInfo(source);
  const stockTags = getStockBrushTagsForSource(source);
  if (metadata || stockSourceInfo) {
    return stockTags;
  }
  const explicitTags = normalizeBrushTags(brush?.tags).map((tag) =>
    STOCK_BRUSH_FOLDER_ID_ALIASES.get(tag.toLocaleLowerCase()) || tag
  );
  return normalizeBrushTags(explicitTags);
}

function getAvailableBrushTags() {
  return getAvailableBrushTagEntries().map((entry) => entry.tag);
}

function getAvailableBrushTagEntries() {
  const tagsByKey = new Map();
  for (const brush of state.brushes) {
    for (const tag of getBrushTags(brush)) {
      const key = tag.toLocaleLowerCase();
      if (!tagsByKey.has(key)) {
        tagsByKey.set(key, { tag, count: 0 });
      }
      tagsByKey.get(key).count += 1;
    }
  }
  return Array.from(tagsByKey.values()).sort((a, b) =>
    a.tag.localeCompare(b.tag, undefined, { numeric: true, sensitivity: "base" })
  );
}

function renderBrushTagMenu(allowOpen = true) {
  if (!brushTagMenuButton || !brushTagMenu) {
    return;
  }

  const tagEntries = getAvailableBrushTagEntries();
  const menuOpen = Boolean(allowOpen && state.brushTagMenuOpen && tagEntries.length);
  state.brushTagMenuOpen = menuOpen;
  brushTagMenuButton.disabled = tagEntries.length === 0;
  brushTagMenuButton.setAttribute("aria-expanded", String(menuOpen));
  brushTagMenuButton.classList.toggle("is-open", menuOpen);
  brushTagMenu.hidden = !menuOpen;
  brushTagMenu.replaceChildren();
  if (!menuOpen) {
    return;
  }

  const currentSearch = normalizeBrushGallerySearch(state.brushGallerySearch).trim();
  const activeSearch = currentSearch.startsWith("#")
    ? currentSearch.slice(1).trim().toLocaleLowerCase()
    : "";
  const fragment = document.createDocumentFragment();
  for (const { tag, count } of tagEntries) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "brush-tag-menu-item";
    button.dataset.brushTag = tag;
    button.setAttribute("role", "menuitem");
    button.title = `Search for #${tag}`;
    const label = document.createElement("span");
    label.className = "brush-tag-menu-label";
    label.textContent = `#${tag}`;
    const countLabel = document.createElement("span");
    countLabel.className = "brush-tag-menu-count";
    countLabel.textContent = `(${count.toLocaleString()})`;
    button.appendChild(label);
    button.appendChild(countLabel);
    const isActive = activeSearch === tag.toLocaleLowerCase();
    button.classList.toggle("is-active", isActive);
    if (isActive) {
      button.setAttribute("aria-current", "true");
    }
    fragment.appendChild(button);
  }
  brushTagMenu.appendChild(fragment);
}

function setBrushTagMenuOpen(nextOpen, options = {}) {
  state.brushTagMenuOpen = Boolean(nextOpen && getAvailableBrushTags().length);
  renderBrushTagMenu(true);
  if (state.brushTagMenuOpen && options.focusFirst) {
    brushTagMenu?.querySelector(".brush-tag-menu-item")?.focus();
  }
}

function applyBrushTagSearch(tag) {
  const normalizedTag = normalizeBrushTags([tag])[0];
  if (!normalizedTag) {
    return;
  }
  state.brushGallerySearch = normalizeBrushGallerySearch(`#${normalizedTag}`);
  resetBrushGalleryPage();
  setBrushTagMenuOpen(false);
  renderBrushGallery();
  brushGallery.scrollTop = 0;
  if (brushGallerySearchInput) {
    brushGallerySearchInput.focus();
    const cursorPosition = brushGallerySearchInput.value.length;
    brushGallerySearchInput.setSelectionRange(cursorPosition, cursorPosition);
  }
  scheduleSessionSave();
}

function normalizeStockBrushFolderId(folderId) {
  const normalizedId = String(folderId || "").trim();
  return STOCK_BRUSH_FOLDER_ID_ALIASES.get(normalizedId.toLocaleLowerCase()) || normalizedId;
}

function getStockBrushFolderById(folderId) {
  const normalizedId = normalizeStockBrushFolderId(folderId);
  return STOCK_BRUSH_FOLDERS.find((folder) => folder && folder.id === normalizedId) || null;
}

function getActiveStockBrushFolderIdSet() {
  if (state.activeStockBrushFolderId === "all") {
    return new Set(
      getOrderedStockBrushFolders()
        .filter((folder) => getStockBrushFiles(folder).length)
        .map((folder) => folder.id)
    );
  }
  if (state.activeStockBrushFolderIds instanceof Set && state.activeStockBrushFolderIds.size) {
    return new Set(
      Array.from(state.activeStockBrushFolderIds).filter((folderId) => getStockBrushFolderById(folderId))
    );
  }
  if (getStockBrushFolderById(state.activeStockBrushFolderId)) {
    return new Set([state.activeStockBrushFolderId]);
  }
  return new Set();
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

  const activeFolderIds = getActiveStockBrushFolderIdSet();
  if (activeFolderIds.size > 1) {
    return Array.from(activeFolderIds)
      .map((folderId) => getStockBrushFolderById(folderId)?.name)
      .filter(Boolean)
      .join("+") || "multi";
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
  if (stockBrushBrowseRow) {
    stockBrushBrowseRow.hidden = !showBrushData || folders.length === 0;
  }
  if (browseAllStockBrushesButton) {
    browseAllStockBrushesButton.disabled = Boolean(state.stockBrushLoadingFolderId) || folders.length === 0;
    browseAllStockBrushesButton.classList.toggle("is-active", state.browsingAllStockBrushes);
    browseAllStockBrushesButton.classList.toggle("is-loading", state.stockBrushLoadingFolderId === "browse-all");
    browseAllStockBrushesButton.setAttribute("aria-pressed", state.browsingAllStockBrushes ? "true" : "false");
  }
  if (loadAllStockBrushesButton) {
    loadAllStockBrushesButton.disabled = Boolean(state.stockBrushLoadingFolderId) || folders.length === 0;
    loadAllStockBrushesButton.classList.toggle("is-active", state.activeStockBrushFolderId === "all");
    loadAllStockBrushesButton.classList.toggle("is-loading", state.stockBrushLoadingFolderId === "all");
    loadAllStockBrushesButton.setAttribute("aria-pressed", state.activeStockBrushFolderId === "all" ? "true" : "false");
  }
  updateFavoriteBrushButtons();
  if (!showBrushData || !folders.length) {
    return;
  }

  const fragment = document.createDocumentFragment();
  const activeFolderIds = getActiveStockBrushFolderIdSet();
  for (const folder of folders) {
    const button = document.createElement("button");
    const iconPath = getStockBrushIconPath(folder);
    const isActive = activeFolderIds.has(folder.id);
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
      icon.src = getStockBrushRequestUrl(encodeStockBrushPath(iconPath));
      icon.alt = "";
      icon.draggable = false;
      icon.loading = "lazy";
      icon.decoding = "async";
      applyGifPauseStateToImage(icon);
      button.appendChild(icon);
    }

    fragment.appendChild(button);
  }

  if (loadAllStockBrushesButton) {
    fragment.appendChild(loadAllStockBrushesButton);
  }

  stockBrushButtons.appendChild(fragment);
}

function getSortedBrushGalleryBrushes() {
  const sortMode = normalizeBrushGallerySort(state.brushGallerySort);
  const searchNeedle = normalizeBrushGallerySearch(state.brushGallerySearch)
    .trim()
    .toLocaleLowerCase();
  const exactTagNeedle = searchNeedle.startsWith("#")
    ? searchNeedle.slice(1).trim()
    : "";
  const brushes = searchNeedle
    ? state.brushes.filter((brush) => {
        const tags = getBrushTags(brush).map((tag) => tag.toLocaleLowerCase());
        if (searchNeedle.startsWith("#")) {
          return Boolean(exactTagNeedle && tags.includes(exactTagNeedle));
        }
        return (
          String(brush.name || "").toLocaleLowerCase().includes(searchNeedle) ||
          tags.some((tag) => tag.includes(searchNeedle))
        );
      })
    : state.brushes.slice();
  const byName = (a, b) => String(a.name || "").localeCompare(String(b.name || ""), undefined, {
    numeric: true,
    sensitivity: "base"
  });

  if (sortMode === "random") {
    const seed = normalizeBrushGalleryRandomSeed(state.brushGalleryRandomSeed);
    if (seed === null) {
      state.brushGalleryRandomSeed = createBrushGalleryRandomSeed();
    }
    const stableSeed = normalizeBrushGalleryRandomSeed(state.brushGalleryRandomSeed) ?? 0;
    brushes.sort((a, b) => {
      const rankDelta =
        getBrushGalleryRandomRank(a, stableSeed) - getBrushGalleryRandomRank(b, stableSeed);
      return rankDelta || byName(a, b) || Number(a.id) - Number(b.id);
    });
    return brushes;
  }

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

function updateBrushGalleryPagination(totalBrushes, totalPages, pageIndex, showGallery) {
  if (!brushGalleryPagination) {
    return;
  }

  const showPagination = showGallery && totalPages > 1;
  brushGalleryPagination.hidden = !showPagination;
  if (!showPagination) {
    return;
  }

  const rangeStart = pageIndex * BRUSH_GALLERY_PAGE_SIZE + 1;
  const rangeEnd = Math.min(totalBrushes, rangeStart + BRUSH_GALLERY_PAGE_SIZE - 1);
  if (brushGalleryPageStatus) {
    brushGalleryPageStatus.textContent =
      `${rangeStart.toLocaleString()}–${rangeEnd.toLocaleString()} of ${totalBrushes.toLocaleString()}` +
      ` · page ${(pageIndex + 1).toLocaleString()}/${totalPages.toLocaleString()}`;
  }
  if (brushGalleryPreviousPageButton) {
    brushGalleryPreviousPageButton.disabled = pageIndex === 0;
  }
  if (brushGalleryNextPageButton) {
    brushGalleryNextPageButton.disabled = pageIndex >= totalPages - 1;
  }
}

function setBrushGalleryPage(pageIndex) {
  const totalPages = Math.max(
    1,
    Math.ceil(getSortedBrushGalleryBrushes().length / BRUSH_GALLERY_PAGE_SIZE)
  );
  const nextPage = clamp(normalizeBrushGalleryPage(pageIndex), 0, totalPages - 1);
  if (nextPage === state.brushGalleryPage) {
    return;
  }
  state.brushGalleryPage = nextPage;
  state.pendingBrushGallerySelectionScroll = false;
  renderBrushGallery();
  brushGallery.scrollTop = 0;
  scheduleSessionSave();
}

function renderBrushGallery() {
  // Every brush/selection mutation is reflected through this renderer. Keep the
  // per-stamp weighted picker hot by rebuilding its pool only after such a change.
  invalidateBrushChoicePool();
  updateBrushDataToggleUI();
  brushGallery.innerHTML = "";
  const showBrushFileMeta = state.sidebarTab === "brushes";
  const activePresetIndex = normalizeCustomBrushPresetIndex(state.activeCustomBrushPresetIndex);
  if (brushSortSelect) {
    brushSortSelect.value = normalizeBrushGallerySort(state.brushGallerySort);
  }
  if (brushGallerySearchInput) {
    const searchValue = normalizeBrushGallerySearch(state.brushGallerySearch);
    if (brushGallerySearchInput.value !== searchValue) {
      brushGallerySearchInput.value = searchValue;
    }
  }

  const showBrushData = !state.brushGalleryCollapsed;
  dropZone.hidden = !showBrushData;
  dropZone.style.display = showBrushData ? "" : "none";
  dropZonePrompt.hidden = !showBrushData;
  unloadBrushDataButton.hidden = !showBrushData;
  if (brushSearchControls) {
    brushSearchControls.hidden = !showBrushData;
  }
  if (brushSortControls) {
    brushSortControls.hidden = !showBrushData;
  }
  renderBrushTagMenu(showBrushData && state.sidebarTab === "brushes");
  if (!showBrushData) {
    dropZone.classList.remove("has-gallery");
    dropZoneHeader.classList.add("no-unload");
    brushGallery.hidden = true;
    updateBrushGalleryPagination(0, 1, 0, false);
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
    state.brushGalleryPage = 0;
    updateBrushGalleryPagination(0, 1, 0, false);
    return;
  }

  const fragment = document.createDocumentFragment();
  const soloBrush = getSoloBrush();
  const selectedBrushes = getSelectedBrushes();
  const selectedBrushIds = new Set(selectedBrushes.map((brush) => brush.id));
  const sortedBrushes = getSortedBrushGalleryBrushes();
  if (!sortedBrushes.length) {
    state.brushGalleryPage = 0;
    updateBrushGalleryPagination(0, 1, 0, false);
    const emptyMessage = document.createElement("p");
    emptyMessage.className = "brush-gallery-empty";
    emptyMessage.setAttribute("role", "status");
    emptyMessage.setAttribute("aria-live", "polite");
    const searchQuery = normalizeBrushGallerySearch(state.brushGallerySearch).trim();
    emptyMessage.textContent = searchQuery
      ? `No GIFs match “${searchQuery}”.`
      : "No GIFs to show.";
    brushGallery.appendChild(emptyMessage);
    return;
  }
  const totalPages = Math.max(1, Math.ceil(sortedBrushes.length / BRUSH_GALLERY_PAGE_SIZE));
  let pageIndex = clamp(normalizeBrushGalleryPage(state.brushGalleryPage), 0, totalPages - 1);
  if (state.pendingBrushGallerySelectionScroll) {
    const pendingBrushId = getSingleSelectedBrushIdForScroll();
    const pendingBrushIndex = sortedBrushes.findIndex((brush) => brush.id === pendingBrushId);
    if (pendingBrushIndex >= 0) {
      pageIndex = Math.floor(pendingBrushIndex / BRUSH_GALLERY_PAGE_SIZE);
    }
  }
  state.brushGalleryPage = pageIndex;
  updateBrushGalleryPagination(sortedBrushes.length, totalPages, pageIndex, true);
  const pageStart = pageIndex * BRUSH_GALLERY_PAGE_SIZE;
  const pageBrushes = sortedBrushes.slice(pageStart, pageStart + BRUSH_GALLERY_PAGE_SIZE);
  for (const brush of pageBrushes) {
    const card = document.createElement("div");
    card.className = "brush-item";
    const isSolo = soloBrush && soloBrush.id === brush.id;
    const isSelected = selectedBrushIds.has(brush.id);
    const isBrowseOnly = state.browsingAllStockBrushes && !brush.enabled;
    if (!brush.enabled && !isBrowseOnly) {
      card.classList.add("is-disabled");
    } else if (isBrowseOnly) {
      card.classList.add("is-browse-only");
    }
    if (isSolo) {
      card.classList.add("is-solo");
    } else if (isSelected) {
      card.classList.add("is-selected");
    } else if (!state.browsingAllStockBrushes && (soloBrush || selectedBrushIds.size)) {
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
    applyBrushGalleryPreviewAnimationState(preview, brush, isBrowseOnly);
    applyBrushTintStyle(preview, !brush.enabled && !isBrowseOnly, NO_TINT_SETTINGS);

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
  scrollBrushGalleryToPendingSingleSelection();
}

function getSingleSelectedBrushIdForScroll() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    return soloBrush.id;
  }
  const selectedBrushes = getSelectedBrushes();
  return selectedBrushes.length === 1 ? selectedBrushes[0].id : null;
}

function scrollBrushGalleryToPendingSingleSelection() {
  if (!state.pendingBrushGallerySelectionScroll || !brushGallery || brushGallery.hidden) {
    return;
  }
  state.pendingBrushGallerySelectionScroll = false;
  const brushId = getSingleSelectedBrushIdForScroll();
  if (!Number.isFinite(Number(brushId))) {
    return;
  }
  const item = brushGallery.querySelector(`.brush-item[data-brush-id="${Number(brushId)}"]`);
  if (!item) {
    return;
  }
  window.requestAnimationFrame(() => {
    item.scrollIntoView({ block: "nearest", inline: "nearest" });
  });
}

function normalizeLayerCustomName(value) {
  if (typeof value !== "string") {
    return "";
  }
  return value.trim().slice(0, 80);
}

function getDefaultStrokeLayerName(stroke) {
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

function getStrokeLayerName(stroke) {
  return normalizeLayerCustomName(stroke?.customName) || getDefaultStrokeLayerName(stroke);
}

function startLayerNameEdit(stroke, nameElement) {
  if (!stroke || !nameElement || nameElement.querySelector(".edit-layer-name-input")) {
    return;
  }

  const previousName = getStrokeLayerName(stroke);
  const previousCustomName = normalizeLayerCustomName(stroke.customName);
  const row = nameElement.closest(".edit-layer-row");
  nameElement.textContent = "";
  nameElement.classList.add("is-editing");
  if (row) {
    row.classList.add("is-renaming");
  }

  const input = document.createElement("input");
  input.type = "text";
  input.className = "edit-layer-name-input";
  input.value = previousName;
  input.maxLength = 80;
  input.setAttribute("aria-label", "Layer name");

  let completed = false;
  const finish = (cancel) => {
    if (completed) {
      return;
    }
    completed = true;
    if (cancel) {
      stroke.customName = previousCustomName;
    } else {
      stroke.customName = normalizeLayerCustomName(input.value);
      scheduleSessionSave();
    }
    markStrokeSerializationDirty(stroke);
    if (row) {
      row.classList.remove("is-renaming");
    }
    renderEditLayers();
  };

  input.addEventListener("pointerdown", (event) => event.stopPropagation());
  input.addEventListener("click", (event) => event.stopPropagation());
  input.addEventListener("dblclick", (event) => event.stopPropagation());
  input.addEventListener("input", () => {
    stroke.customName = normalizeLayerCustomName(input.value);
    markStrokeSerializationDirty(stroke);
  });
  input.addEventListener("keydown", (event) => {
    if (event.key === "Enter") {
      event.preventDefault();
      finish(false);
    } else if (event.key === "Escape") {
      event.preventDefault();
      finish(true);
    }
  });
  input.addEventListener("blur", () => finish(false));

  nameElement.appendChild(input);
  window.requestAnimationFrame(() => {
    input.focus();
    input.select();
  });
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
  markStrokeSerializationDirty(stroke);
  invalidateStampOcclusion();

  const hidden = Boolean(stroke.hidden);
  resetLayerSequencePreviewRuntime(stroke);
  resetStrokeSequenceRuntime(stroke);
  const viewportBounds = getViewportVisibilityBounds();
  for (const element of stroke.elements) {
    resetStampSequenceStyle(element);
    element.classList.toggle("is-layer-hidden", hidden);
    if (hidden) {
      state.viewportRenderedStamps.delete(element);
      unregisterStampSpatialCells(element);
    } else if (element.parentElement === world) {
      registerStampSpatialCells(element);
      updateStampViewportVisibility(element, viewportBounds);
    }
  }
  updateUndoState();
  scheduleStampVisibilityRefresh();
  refreshLayerSequenceLoop();
  syncSceneRendererElements(stroke.elements);
}

function applyStrokeAnimationPaused(stroke) {
  if (!stroke || !Array.isArray(stroke.elements)) {
    return;
  }
  markStrokeSerializationDirty(stroke);
  setStrokeSequenceClockPaused(
    stroke,
    Boolean(stroke.animationPaused || state.gifAnimationsPaused),
    performance.now()
  );

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
  refreshLayerSequenceLoop();
  syncSceneRendererElements(stroke.elements);
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
  if (effect === "pixelate") {
    return getPixelateDurationMs(settings);
  }
  if (effect === "blur") {
    return getBlurDurationMs(settings);
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

function getPixelateDurationMs(settings) {
  return mapSequenceSlider(settings.pixelateSpeed, 5000, 50);
}

function getBlurDurationMs(settings) {
  return mapSequenceSlider(settings.blurSpeed, 5000, 50);
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
  return mapCompressedSequenceSlider("randomSpeed", settings.randomSpeed, 4000, 50);
}

function resetStrokeSequenceRuntime(stroke) {
  if (!stroke) {
    return;
  }
  stroke.sequenceRuntime = null;
  stroke.sequenceSlotRuntimes = null;
  delete stroke.sequencePauseStartTime;
}

function invalidateStrokeSequenceTopology(stroke) {
  if (!stroke || typeof stroke !== "object") {
    return;
  }
  stroke.sequenceTopologyRevision =
    (Math.max(0, Math.floor(Number(stroke.sequenceTopologyRevision)) || 0) + 1) %
    Number.MAX_SAFE_INTEGER;
  stroke.sequenceRuntime = null;
  stroke.sequenceSlotRuntimes = null;
  resetLayerSequencePreviewRuntime(stroke);
}

function resetLayerSequencePreviewRuntime(stroke) {
  if (stroke) {
    layerSequencePreviewRuntimeByStroke.delete(stroke);
  }
}

function shiftSequenceDatasetClock(dataset, offsetMs) {
  if (!dataset || typeof dataset !== "object" || !Number.isFinite(offsetMs) || offsetMs <= 0) {
    return;
  }
  for (const key of Object.keys(dataset)) {
    if (
      key.endsWith("Start") ||
      key.endsWith("StartTime") ||
      key.endsWith("MoveStart") ||
      key.endsWith("RotateStart") ||
      key.endsWith("ScaleStart") ||
      key.endsWith("ColorStart") ||
      key.endsWith("VisibilityStart")
    ) {
      const value = Number(dataset[key]);
      if (Number.isFinite(value)) {
        dataset[key] = String(value + offsetMs);
      }
    }
  }
}

function shiftSequenceRuntimeClock(runtime, offsetMs) {
  if (!runtime || typeof runtime !== "object" || !Number.isFinite(offsetMs) || offsetMs <= 0) {
    return;
  }
  if (Number.isFinite(Number(runtime.pulseBaseTime))) {
    runtime.pulseBaseTime += offsetMs;
  }
  if (Number.isFinite(Number(runtime.baseTime))) {
    runtime.baseTime += offsetMs;
  }
  if (Number.isFinite(Number(runtime.nextTriggerTime))) {
    runtime.nextTriggerTime += offsetMs;
  }
  shiftSequenceDatasetClock(runtime.groupDataset, offsetMs);
}

function shiftStrokeSequenceClock(stroke, offsetMs) {
  if (!stroke || !Number.isFinite(offsetMs) || offsetMs <= 0) {
    return;
  }
  shiftSequenceRuntimeClock(stroke.sequenceRuntime, offsetMs);
  if (Array.isArray(stroke.sequenceSlotRuntimes)) {
    for (const runtime of stroke.sequenceSlotRuntimes) {
      shiftSequenceRuntimeClock(runtime, offsetMs);
    }
  }
  for (const stamp of stroke.elements || []) {
    shiftSequenceDatasetClock(stamp?.dataset, offsetMs);
  }
}

function shiftLayerSequencePreviewClock(stroke, offsetMs) {
  if (!stroke || !Number.isFinite(offsetMs) || offsetMs <= 0) {
    return;
  }
  const slots = layerSequencePreviewRuntimeByStroke.get(stroke);
  if (!Array.isArray(slots)) {
    return;
  }
  for (const slotState of slots) {
    if (!slotState || !Array.isArray(slotState.buckets)) {
      continue;
    }
    for (const bucket of slotState.buckets) {
      if (Number.isFinite(bucket.firedAt)) {
        bucket.firedAt += offsetMs;
      }
    }
    slotState.pausedAt = null;
  }
}

function setStrokeSequenceClockPaused(stroke, paused, now = performance.now()) {
  if (!stroke) {
    return;
  }
  if (paused) {
    if (!Number.isFinite(Number(stroke.sequencePauseStartTime))) {
      stroke.sequencePauseStartTime = now;
    }
    return;
  }
  if (Number.isFinite(Number(stroke.sequencePauseStartTime))) {
    const pausedDuration = Math.max(0, now - Number(stroke.sequencePauseStartTime));
    shiftStrokeSequenceClock(stroke, pausedDuration);
    shiftLayerSequencePreviewClock(stroke, pausedDuration);
    delete stroke.sequencePauseStartTime;
  }
}

function shiftAllLayerSequenceClocks(offsetMs) {
  if (!Number.isFinite(offsetMs) || offsetMs <= 0) {
    return;
  }
  for (const stroke of state.strokes) {
    shiftStrokeSequenceClock(stroke, offsetMs);
  }
}

function cancelScheduledStrokeSequenceEffectRefresh(stroke) {
  const timeoutId = pendingLayerSequenceRefreshByStroke.get(stroke);
  if (timeoutId === undefined) {
    return;
  }
  window.clearTimeout(timeoutId);
  pendingLayerSequenceRefreshByStroke.delete(stroke);
}

function scheduleStrokeSequenceEffectRefresh(stroke) {
  if (!stroke) {
    return;
  }
  cancelScheduledStrokeSequenceEffectRefresh(stroke);
  const timeoutId = window.setTimeout(() => {
    pendingLayerSequenceRefreshByStroke.delete(stroke);
    if (state.strokeById.get(Number(stroke.id)) === stroke) {
      refreshStrokeSequenceEffect(stroke);
    }
  }, LAYER_SEQUENCE_SETTING_RESET_DEBOUNCE_MS);
  pendingLayerSequenceRefreshByStroke.set(stroke, timeoutId);
}

function refreshStrokeSequenceEffect(stroke) {
  if (!stroke) {
    return;
  }
  cancelScheduledStrokeSequenceEffectRefresh(stroke);
  markStrokeSerializationDirty(stroke);
  invalidateStampOcclusion();
  resetLayerSequencePreviewRuntime(stroke);
  resetStrokeSequenceEffect(stroke);
  refreshLayerSequenceLoop();
  scheduleStampOcclusionRefresh();
  syncSceneRendererElements(stroke.elements);
}

function resetStrokeSequenceEffect(stroke) {
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
  if (!Number.isFinite(baseTime)) {
    return now;
  }
  if (baseTime > now) {
    runtime.baseTime = now;
    return now;
  }
  return baseTime;
}

function getStrokeSequenceTopologyKey(stroke) {
  return Math.max(0, Math.floor(Number(stroke?.sequenceTopologyRevision)) || 0);
}

function createSequenceTriggerKey(stroke, style, ...parts) {
  return `${style}:t${getStrokeSequenceTopologyKey(stroke)}:${parts.join(":")}`;
}

function getPulseLayerSequenceTriggers(
  stroke,
  index,
  total,
  settings,
  now,
  effectDuration,
  runtimeHost
) {
  if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== "pulse") {
    runtimeHost.sequenceRuntime = {
      style: "pulse",
      pulseBaseTime: now,
      triggeredPulseByIndex: [],
      frameTime: NaN,
      remainingCatchUpTriggers: LAYER_SEQUENCE_MAX_PULSE_CATCH_UP_PER_FRAME
    };
  }
  const runtime = runtimeHost.sequenceRuntime;
  if (!Array.isArray(runtime.triggeredPulseByIndex)) {
    runtime.triggeredPulseByIndex = [];
  }
  if (runtime.frameTime !== now) {
    runtime.frameTime = now;
    runtime.remainingCatchUpTriggers = LAYER_SEQUENCE_MAX_PULSE_CATCH_UP_PER_FRAME;
  }
  if (Number(runtime.pulseBaseTime) > now) {
    runtime.pulseBaseTime = now;
  }
  const spacing = getPulseSpacingMs(settings);
  const interval = Math.max(16, getPulseIntervalMs(settings));
  const maxDuePulseId = Math.floor(
    (now - runtime.pulseBaseTime - index * spacing) / interval
  );
  const lastPulseForIndex = Number.isFinite(Number(runtime.triggeredPulseByIndex[index]))
    ? Number(runtime.triggeredPulseByIndex[index])
    : -1;
  const availableTriggerCount = Math.max(0, maxDuePulseId - lastPulseForIndex);
  const triggerCount = Math.min(
    availableTriggerCount,
    LAYER_SEQUENCE_MAX_PULSE_CATCH_UP_PER_STAMP,
    Math.max(0, Math.floor(Number(runtime.remainingCatchUpTriggers)) || 0)
  );
  if (!triggerCount) {
    return [];
  }

  const triggers = [];
  for (let offset = 1; offset <= triggerCount; offset += 1) {
    const pulseId = lastPulseForIndex + offset;
    const startTime = runtime.pulseBaseTime + pulseId * interval + index * spacing;
    triggers.push({
      active: true,
      key: createSequenceTriggerKey(stroke, "pulse", pulseId, index),
      startTime,
      endTime: startTime + Math.max(16, effectDuration)
    });
  }
  runtime.triggeredPulseByIndex[index] = lastPulseForIndex + triggerCount;
  runtime.remainingCatchUpTriggers -= triggerCount;
  return triggers;
}

function advanceWaveSequenceRuntime(runtime, safeTotal, settings) {
  const triggerIndex = clamp(
    Math.floor(Number(runtime.nextIndex)) || 0,
    0,
    safeTotal - 1
  );
  runtime.nextIndex = triggerIndex;
  const bounceId = Math.max(0, Math.floor(Number(runtime.bounceId)) || 0);
  runtime.bounceId = bounceId + 1;
  if (safeTotal <= 1) {
    runtime.nextIndex = 0;
    runtime.direction = settings.waveReverse ? -1 : 1;
    runtime.repeatEndpointIndex = 0;
    runtime.hasLeftInitialEndpoint = true;
    return { triggerIndex, bounceId };
  }

  const initialIndex = clamp(
    Math.floor(Number(runtime.initialIndex)) || 0,
    0,
    safeTotal - 1
  );
  runtime.initialIndex = initialIndex;
  const isEndpoint = triggerIndex <= 0 || triggerIndex >= safeTotal - 1;
  const isInitialEndpoint =
    triggerIndex === initialIndex && runtime.hasLeftInitialEndpoint !== true;
  if (Number(runtime.repeatEndpointIndex) === triggerIndex) {
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
      runtime.hasLeftInitialEndpoint || triggerIndex !== initialIndex;
    let nextIndex = triggerIndex + (Number(runtime.direction) < 0 ? -1 : 1);
    if (nextIndex >= safeTotal) {
      runtime.direction = -1;
      nextIndex = safeTotal - 1;
    } else if (nextIndex < 0) {
      runtime.direction = 1;
      nextIndex = 0;
    }
    runtime.nextIndex = clamp(nextIndex, 0, safeTotal - 1);
  }
  return { triggerIndex, bounceId };
}

function getWaveLayerSequenceTriggers(
  stroke,
  index,
  total,
  settings,
  now,
  effectDuration,
  runtimeHost
) {
  const safeTotal = Math.max(1, total);
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
      frameTime: NaN,
      frameTriggersByIndex: new Map(),
      total: safeTotal
    };
  }
  const runtime = runtimeHost.sequenceRuntime;
  if (runtime.total !== safeTotal) {
    runtime.total = safeTotal;
    runtime.nextIndex = clamp(
      Math.floor(Number(runtime.nextIndex)) || 0,
      0,
      safeTotal - 1
    );
    runtime.initialIndex = clamp(
      Math.floor(Number(runtime.initialIndex)) || 0,
      0,
      safeTotal - 1
    );
    runtime.repeatEndpointIndex = null;
  }
  if (runtime.frameTime !== now) {
    runtime.frameTime = now;
    runtime.frameTriggersByIndex = new Map();
    const spacing = getWaveSpacingMs(settings);
    if (
      !Number.isFinite(Number(runtime.nextTriggerTime)) ||
      Number(runtime.nextTriggerTime) > now + spacing * 2
    ) {
      runtime.nextTriggerTime = now;
    }
    const oldestCatchUpTime = now - spacing * (LAYER_SEQUENCE_MAX_WAVE_CATCH_UP_PER_FRAME - 1);
    if (runtime.nextTriggerTime < oldestCatchUpTime) {
      runtime.nextTriggerTime = oldestCatchUpTime;
    }
    let triggerCount = 0;
    while (
      runtime.nextTriggerTime <= now &&
      triggerCount < LAYER_SEQUENCE_MAX_WAVE_CATCH_UP_PER_FRAME
    ) {
      const startTime = runtime.nextTriggerTime;
      const { triggerIndex, bounceId } = advanceWaveSequenceRuntime(
        runtime,
        safeTotal,
        settings
      );
      const triggers = runtime.frameTriggersByIndex.get(triggerIndex) || [];
      triggers.push({
        active: true,
        key: createSequenceTriggerKey(stroke, "wave", bounceId, triggerIndex),
        startTime,
        endTime: startTime + Math.max(16, effectDuration)
      });
      runtime.frameTriggersByIndex.set(triggerIndex, triggers);
      runtime.nextTriggerTime = startTime + spacing;
      triggerCount += 1;
    }
  }
  return runtime.frameTriggersByIndex instanceof Map
    ? runtime.frameTriggersByIndex.get(index) || []
    : [];
}

function getLayerSequenceTriggers(
  stroke,
  index,
  total,
  style,
  settings,
  now,
  effectDuration,
  runtimeHost = stroke
) {
  if (style === "pulse") {
    return getPulseLayerSequenceTriggers(
      stroke,
      index,
      total,
      settings,
      now,
      effectDuration,
      runtimeHost
    );
  }
  if (style === "wave") {
    return getWaveLayerSequenceTriggers(
      stroke,
      index,
      total,
      settings,
      now,
      effectDuration,
      runtimeHost
    );
  }
  const trigger = getLayerSequenceTrigger(
    stroke,
    index,
    total,
    style,
    settings,
    now,
    effectDuration,
    runtimeHost
  );
  return trigger.active ? [trigger] : [];
}

function getLayerSequenceTrigger(stroke, index, total, style, settings, now, effectDuration, runtimeHost = stroke) {
  const safeTotal = Math.max(1, total);
  if (style === "pulse") {
    return getPulseLayerSequenceTriggers(
      stroke,
      index,
      total,
      settings,
      now,
      effectDuration,
      runtimeHost
    )[0] || { active: false, key: "", startTime: 0, endTime: 0 };
  }

  if (runtimeHost.sequenceRuntime && runtimeHost.sequenceRuntime.style !== style) {
    resetStrokeSequenceRuntime(runtimeHost);
  }

  if (style === "all" || style === "grouped") {
    if (!runtimeHost.sequenceRuntime || runtimeHost.sequenceRuntime.style !== style) {
      runtimeHost.sequenceRuntime = {
        style,
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
      key: createSequenceTriggerKey(stroke, style, tick),
      startTime,
      endTime: startTime + interval
    };
  }

  if (style === "wave") {
    return getWaveLayerSequenceTriggers(
      stroke,
      index,
      total,
      settings,
      now,
      effectDuration,
      runtimeHost
    )[0] || { active: false, key: "", startTime: 0, endTime: 0 };
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
    const stepRate = Math.max(50, settings.stepRate);
    const stepAmount = Math.max(1, Math.round(settings.stepAmount));
    const baseTime = getSequenceRuntimeBaseTime(runtime, now);
    const elapsed = Math.max(0, now - baseTime);
    const tick = Math.floor(elapsed / stepRate);
    const tickElapsed = elapsed - tick * stepRate;
    const start = (tick * stepAmount) % safeTotal;
    const offset = (index - start + safeTotal) % safeTotal;
    const active = tickElapsed <= stepLength && offset < Math.min(stepAmount, safeTotal);
    const startTime = baseTime + tick * stepRate;
    return {
      active,
      key: createSequenceTriggerKey(stroke, style, tick),
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
      key: createSequenceTriggerKey(stroke, style, tick),
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
  if (!stamp.dataset.sequenceBaseImageRendering) {
    stamp.dataset.sequenceBaseImageRendering = stamp.style.imageRendering || "pixelated";
  }
  if (!stamp.dataset.sequenceDisplayedSource) {
    stamp.dataset.sequenceDisplayedSource =
      stamp.dataset.sequenceBaseSrc || stamp.dataset.brushUrl || stamp.getAttribute("src") || "";
  }
}

function getStampBaseTintSettings(stamp) {
  return normalizeTintSettings({
    color: stamp?.dataset?.tintColor || "#ffffff",
    amountPercent: Number(stamp?.dataset?.tintAmount) || 0
  });
}

function getIsolatedSequenceGifSource(stamp, src) {
  if (!stamp || !isGifUrl(src)) {
    return src;
  }
  const strokeId = String(stamp.dataset.strokeId || "0").replace(/[^a-z0-9_-]/gi, "");
  const brushId = String(stamp.dataset.brushId || "0").replace(/[^a-z0-9_-]/gi, "");
  const token = `seq-stamp-${strokeId}-${brushId}-${Array.prototype.indexOf.call(stamp.parentNode?.children || [], stamp)}`;
  return `${src}${src.includes("#") ? "&" : "#"}${token}`;
}

function setStampSequenceImage(stamp, src, isolateGifPlayback = false) {
  if (!src) {
    return;
  }
  if (!state.sequenceExportActive && isRenderCulledStamp(stamp)) {
    stamp.dataset.sequenceDisplayedSource = src;
    return;
  }
  if (!state.sequenceExportActive && isSceneRendererStampSuppressed(stamp)) {
    stamp.dataset.sequenceDisplayedSource = src;
    markGifPlaybackStart(stamp, src);
    return;
  }
  if (
    stamp.dataset.sequenceDisplayedSource === src &&
    (isolateGifPlayback || stamp.getAttribute("src") === src)
  ) {
    return;
  }
  const displaySrc = isolateGifPlayback ? getIsolatedSequenceGifSource(stamp, src) : src;
  stamp.dataset.sequenceDisplayedSource = src;
  stamp.src = displaySrc;
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
  const baseOpacity = stamp.dataset.sequenceBaseOpacity;
  const baseSource = stamp.dataset.sequenceBaseSrc || stamp.dataset.brushUrl || stamp.getAttribute("src") || "";
  const baseImageRendering = stamp.dataset.sequenceBaseImageRendering || stamp.style.imageRendering || "pixelated";
  deleteSequenceRuntimeDataset(stamp);
  if (baseOpacity) {
    stamp.dataset.sequenceBaseOpacity = baseOpacity;
  }
  if (baseSource) {
    stamp.dataset.sequenceBaseSrc = baseSource;
    stamp.dataset.sequenceDisplayedSource = baseSource;
  }
  if (baseImageRendering) {
    stamp.dataset.sequenceBaseImageRendering = baseImageRendering;
    stamp.style.imageRendering = baseImageRendering;
  }
  removeSequencePixelateProxy(stamp);
  const stroke = getStampLayerStroke(stamp);
  applyStampLayerVisualStyle(stroke, stamp);
  applyBrushTintStyle(stamp, false, getStampBaseTintSettings(stamp));
  setStampSequenceImage(stamp, baseSource);
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

function getCurrentSequenceScalarAmount(stamp, prefix, durationMs, now, maxValue) {
  const target = Number(stamp.dataset[`${prefix}To`]);
  const startTime = Number(stamp.dataset[`${prefix}Start`]);
  const from = Number(stamp.dataset[`${prefix}From`]);
  const to = Number(stamp.dataset[`${prefix}To`]);
  if (!Number.isFinite(startTime) || !Number.isFinite(from) || !Number.isFinite(to)) {
    return Number.isFinite(target) ? clamp(target, 0, maxValue) : 0;
  }
  const duration = Number.isFinite(Number(stamp.dataset[`${prefix}Duration`]))
    ? Math.max(1, Number(stamp.dataset[`${prefix}Duration`]))
    : Math.max(1, durationMs);
  const progress = clamp((now - startTime) / duration, 0, 1);
  const eased = progress < 0.5
    ? 2 * progress * progress
    : 1 - Math.pow(-2 * progress + 2, 2) / 2;
  const amount = from + (to - from) * eased;
  if (progress >= 1) {
    stamp.dataset[`${prefix}From`] = String(to);
    stamp.dataset[`${prefix}To`] = String(to);
    stamp.dataset[`${prefix}Target`] = String(to);
    delete stamp.dataset[`${prefix}Start`];
    delete stamp.dataset[`${prefix}Duration`];
    return clamp(to, 0, maxValue);
  }
  return clamp(amount, 0, maxValue);
}

function getCurrentSequencePixelateAmount(stamp, settings, now) {
  return getCurrentSequenceScalarAmount(stamp, "sequencePixelate", getPixelateDurationMs(settings), now, 64);
}

function getCurrentSequenceBlurAmount(stamp, settings, now) {
  return getCurrentSequenceScalarAmount(stamp, "sequenceBlur", getBlurDurationMs(settings), now, 64);
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
    return false;
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
  } else if (effect === "pixelate") {
    const currentAmount = getCurrentSequencePixelateAmount(stamp, settings, now);
    const nextPixelated = stamp.dataset.sequencePixelated !== "1";
    const targetAmount = nextPixelated ? settings.pixelateAmount : 0;
    stamp.dataset.sequencePixelateStart = String(triggerStartTime);
    stamp.dataset.sequencePixelateFrom = String(currentAmount);
    stamp.dataset.sequencePixelateTo = String(targetAmount);
    stamp.dataset.sequencePixelateTarget = String(targetAmount);
    stamp.dataset.sequencePixelateDuration = String(getPixelateDurationMs(settings));
    stamp.dataset.sequencePixelated = nextPixelated ? "1" : "0";
  } else if (effect === "blur") {
    const currentAmount = getCurrentSequenceBlurAmount(stamp, settings, now);
    const nextBlurred = stamp.dataset.sequenceBlurred !== "1";
    const targetAmount = nextBlurred ? settings.blurAmount : 0;
    stamp.dataset.sequenceBlurStart = String(triggerStartTime);
    stamp.dataset.sequenceBlurFrom = String(currentAmount);
    stamp.dataset.sequenceBlurTo = String(targetAmount);
    stamp.dataset.sequenceBlurTarget = String(targetAmount);
    stamp.dataset.sequenceBlurDuration = String(getBlurDurationMs(settings));
    stamp.dataset.sequenceBlurred = nextBlurred ? "1" : "0";
  } else if (effect === "image-cycle") {
    triggerImageCycleSequence(stamp, trigger, settings, pool, index, currentSource);
  }
  return true;
}

function ensureGroupedSequenceTransform(visual) {
  if (!visual.groupedTransform) {
    visual.groupedTransform = {
      moveX: 0,
      moveY: 0,
      rotationOffset: 0,
      scale: 1
    };
  }
  return visual.groupedTransform;
}

function applyGroupedSequenceEffectToVisual(visual, effect, groupStamp, settings, now) {
  if (!visual) {
    return;
  }
  if (effect === "move") {
    const move = getCurrentSequenceMove(groupStamp, settings, now);
    const transform = ensureGroupedSequenceTransform(visual);
    transform.moveX += move.x;
    transform.moveY += move.y;
  } else if (effect === "rotate") {
    const transform = ensureGroupedSequenceTransform(visual);
    transform.rotationOffset += getCurrentSequenceRotation(groupStamp, settings, now);
  } else if (effect === "scale") {
    const transform = ensureGroupedSequenceTransform(visual);
    transform.scale *= getCurrentSequenceScale(groupStamp, settings, now);
  } else if (effect === "pixelate") {
    visual.pixelateAmount = Math.max(
      visual.pixelateAmount,
      Math.round(getCurrentSequencePixelateAmount(groupStamp, settings, now))
    );
  } else if (effect === "blur") {
    visual.blurAmount += getCurrentSequenceBlurAmount(groupStamp, settings, now);
  }
}

function runLayerSequences(now = performance.now(), activeStrokes = null) {
  const strokes = Array.isArray(activeStrokes) ? activeStrokes : state.strokes;
  const rendererElementsToSync = [];
  const needsImageCyclePool = strokes.some((stroke) =>
    isLayerSequenceEnabled(stroke) &&
      getLayerSequenceSlots(stroke).some((slot) => slot.effect === "image-cycle")
  );
  const imageCyclePool = needsImageCyclePool ? getSequenceBrushPool() : [];
  for (const stroke of strokes) {
    try {
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
        setStrokeSequenceClockPaused(stroke, false, now);
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

      const layerBaseOpacity = getLayerOpacityFraction(stroke);
      const total = stroke.elements.length;
      const visuals = stroke.elements.map((stamp) => {
        if (!(stamp instanceof HTMLImageElement)) {
          return null;
        }
        ensureStampSequenceBase(stamp);
        if (stamp.dataset.sequenceActive !== "1") {
          stamp.dataset.sequenceActive = "1";
        }
        return {
          opacity: layerBaseOpacity,
          moveX: 0,
          moveY: 0,
          rotationOffset: 0,
          scale: 1,
          groupedTransform: null,
          tintSettings: getStampBaseTintSettings(stamp),
          pixelateAmount: 0,
          blurAmount: 0,
          baseImageRendering: stamp.dataset.sequenceBaseImageRendering || stamp.style.imageRendering || "pixelated",
          sourceUrl: stamp.dataset.sequenceBaseSrc || stamp.dataset.brushUrl || stamp.getAttribute("src") || "",
          imageCycleSource: false
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
          sequenceRuntime: stroke.sequenceSlotRuntimes[slotIndex] || null
        };
        const previewCapture = createLayerSequencePreviewCapture(
          stroke,
          slotIndex,
          total,
          effect,
          timingStyle,
          settings,
          effectDuration
        );
        let recordedAllPreviewImpulse = false;

        if (timingStyle === "grouped" && isGroupedLayerSequenceEffect(effect)) {
          const trigger = getLayerSequenceTrigger(
            stroke,
            0,
            total,
            timingStyle,
            settings,
            now,
            effectDuration,
            runtimeHost
          );
          if (!runtimeHost.sequenceRuntime) {
            runtimeHost.sequenceRuntime = {
              style: "grouped",
              baseTime: now
            };
          }
          if (
            !runtimeHost.sequenceRuntime.groupDataset ||
            typeof runtimeHost.sequenceRuntime.groupDataset !== "object"
          ) {
            runtimeHost.sequenceRuntime.groupDataset = {};
          }
          const groupStamp = { dataset: runtimeHost.sequenceRuntime.groupDataset };
          const didTrigger = triggerStampSequenceEffect(
            groupStamp,
            effect,
            trigger,
            settings,
            imageCyclePool,
            0,
            now,
            ""
          );
          if (didTrigger && claimLayerSequencePreviewImpulse(previewCapture, 0, trigger, true)) {
            recordLayerSequencePreviewImpulse(
              previewCapture,
              0,
              trigger,
              now,
              true
            );
          }
          for (const visual of visuals) {
            applyGroupedSequenceEffectToVisual(visual, effect, groupStamp, settings, now);
          }
          stroke.sequenceSlotRuntimes[slotIndex] = runtimeHost.sequenceRuntime;
          continue;
        }

        for (let index = 0; index < total; index += 1) {
          const stamp = stroke.elements[index];
          const visual = visuals[index];
          if (!stamp || stamp.parentElement !== world || !visual) {
            continue;
          }
          const runtimeStamp = createSequenceSlotRuntimeStamp(stamp, slotIndex);
          let currentImageCycleSource = effect === "image-cycle"
            ? getCurrentSequenceImageSource(runtimeStamp, visual.sourceUrl)
            : visual.sourceUrl;

          const triggers = getLayerSequenceTriggers(
            stroke,
            index,
            total,
            timingStyle,
            settings,
            now,
            effectDuration,
            runtimeHost
          );
          for (const trigger of triggers) {
            const didTrigger = triggerStampSequenceEffect(
              runtimeStamp,
              effect,
              trigger,
              settings,
              imageCyclePool,
              index,
              now,
              currentImageCycleSource
            );
            if (didTrigger && effect === "image-cycle") {
              currentImageCycleSource = getCurrentSequenceImageSource(
                runtimeStamp,
                currentImageCycleSource
              );
            }
            if (didTrigger && (timingStyle !== "all" || !recordedAllPreviewImpulse)) {
              const activateAll = timingStyle === "all";
              if (claimLayerSequencePreviewImpulse(previewCapture, index, trigger, activateAll)) {
                recordLayerSequencePreviewImpulse(
                  previewCapture,
                  index,
                  trigger,
                  now,
                  activateAll
                );
              }
              recordedAllPreviewImpulse = recordedAllPreviewImpulse || activateAll;
            }
          }

          if (effect === "show-hide") {
            const baseOpacity = layerBaseOpacity;
            const currentOpacity = clamp(getCurrentSequenceOpacity(runtimeStamp, settings, now), 0, 1);
            const opacityFactor = baseOpacity > 0 ? currentOpacity / baseOpacity : currentOpacity;
            visual.opacity *= clamp(opacityFactor, 0, 1);
          } else if (effect === "move") {
            const move = getCurrentSequenceMove(runtimeStamp, settings, now);
            visual.moveX += move.x;
            visual.moveY += move.y;
          } else if (effect === "rotate") {
            visual.rotationOffset += getCurrentSequenceRotation(runtimeStamp, settings, now);
          } else if (effect === "scale") {
            visual.scale *= getCurrentSequenceScale(runtimeStamp, settings, now);
          } else if (effect === "color-cycle") {
            const amount = getCurrentSequenceColorAmount(runtimeStamp, settings, now);
            if (amount > 0) {
              visual.tintSettings = createLayeredTintSettings(visual.tintSettings, {
                color: settings.colorCycleColor,
                amountPercent: amount
              });
            }
          } else if (effect === "pixelate") {
            visual.pixelateAmount = Math.max(
              visual.pixelateAmount,
              Math.round(getCurrentSequencePixelateAmount(runtimeStamp, settings, now))
            );
          } else if (effect === "blur") {
            visual.blurAmount += getCurrentSequenceBlurAmount(runtimeStamp, settings, now);
          } else if (effect === "image-cycle") {
            visual.sourceUrl = getCurrentSequenceImageSource(runtimeStamp, currentImageCycleSource);
            visual.imageCycleSource = true;
          }

          commitSequenceSlotRuntimeStamp(stamp, slotIndex, runtimeStamp);
        }

        stroke.sequenceSlotRuntimes[slotIndex] = runtimeHost.sequenceRuntime;
      }

      const sequenceVisibilityBounds =
        !state.sequenceExportActive && strokeHasActiveSequenceTransform(stroke)
          ? getViewportVisibilityBounds()
          : null;
      for (let index = 0; index < total; index += 1) {
        const stamp = stroke.elements[index];
        const visual = visuals[index];
        if (!stamp || stamp.parentElement !== world || !visual) {
          continue;
        }
        if (sequenceVisibilityBounds) {
          setStampOcclusionCulled(stamp, false);
          const targetBounds = isViewportCulledStamp(stamp)
            ? sequenceVisibilityBounds.show
            : sequenceVisibilityBounds.hide;
          setStampViewportRendered(
            stamp,
            rectsIntersect(
              getStampSequenceVisualWorldBounds(stroke, stamp, visual),
              targetBounds
            )
          );
        }
        if (!state.sequenceExportActive && isRenderCulledStamp(stamp)) {
          continue;
        }
        setStampSequenceImage(stamp, visual.sourceUrl, visual.imageCycleSource);
        setInlineStyleIfChanged(
          stamp,
          "imageRendering",
          visual.pixelateAmount > 0 ? "pixelated" : visual.baseImageRendering
        );
        const layerTransform = visual.groupedTransform
          ? getStampGroupedLayerTransform(stroke, stamp, visual.groupedTransform)
          : getStampLayerTransform(stroke, stamp);
        const baseRotation = Number(stamp.dataset.rotation) || 0;
        const moveX = layerTransform.x + visual.moveX;
        const moveY = layerTransform.y + visual.moveY;
        const rotation = baseRotation + layerTransform.rotation + visual.rotationOffset;
        const scale = layerTransform.scale * visual.scale;
        setInlineStyleIfChanged(
          stamp,
          "transform",
          `translate(${moveX}px, ${moveY}px) rotate(${rotation}deg) scale(${scale})`
        );
        const usingPixelateProxy = syncSequencePixelateProxy(stamp, visual);
        applyBrushTintStyle(stamp, false, visual.tintSettings, {
          blurAmount: usingPixelateProxy ? 0 : visual.blurAmount
        });
        setInlineStyleIfChanged(
          stamp,
          "opacity",
          usingPixelateProxy ? "0" : String(clamp(visual.opacity, 0, 1))
        );
      }
      if (state.sceneRendererActive || state.sceneRendererPreparing) {
        rendererElementsToSync.push(...stroke.elements);
      }
    } catch (error) {
      console.warn("Layer sequence skipped for stroke.", error);
      resetStrokeSequenceRuntime(stroke);
    }
  }
  if (rendererElementsToSync.length) {
    syncSceneRendererElements(rendererElementsToSync);
  }
}

function applyLayerSequences(now = performance.now()) {
  state.sequenceRafId = null;
  try {
    if (state.sequenceExportActive && !state.exportTask) {
      state.sequenceExportActive = false;
    }
    if (!state.sequenceExportActive) {
      const activeStrokes = getTrackedActiveSequenceStrokes();
      const frameInterval = getAdaptiveSequenceFrameIntervalMs(activeStrokes);
      const lastFrameTime = Number(state.sequenceLastFrameTime);
      const frameIsDue =
        !Number.isFinite(lastFrameTime) ||
        frameInterval <= 0 ||
        now - lastFrameTime >= frameInterval;
      if (activeStrokes.length && frameIsDue) {
        runLayerSequences(now, activeStrokes);
        state.sequenceLastFrameTime = now;
      }
    }
  } catch (error) {
    console.warn("Layer sequence frame skipped.", error);
  } finally {
    renderLayerSequencePreviews(now);
    if (!state.sequenceExportActive && state.sequenceActiveStrokeIds.size) {
      state.sequenceRafId = window.requestAnimationFrame(applyLayerSequences);
    }
  }
}

function startLayerSequenceLoop() {
  if (!state.sequenceActiveStrokeIds.size) {
    const activeStrokes = getActiveSequenceStrokes();
    state.sequenceActiveStrokeIds = new Set(activeStrokes.map((stroke) => stroke.id));
  }
  if (
    state.sequenceRafId !== null ||
    state.sequenceExportActive ||
    !state.sequenceActiveStrokeIds.size
  ) {
    return;
  }
  state.sequenceRafId = window.requestAnimationFrame(applyLayerSequences);
}

function stopLayerSequenceLoop() {
  if (state.sequenceRafId !== null) {
    window.cancelAnimationFrame(state.sequenceRafId);
    state.sequenceRafId = null;
  }
  state.sequenceActiveStrokeIds.clear();
  state.sequenceLastFrameTime = null;
  renderLayerSequencePreviews(performance.now(), { force: true });
}

function refreshLayerSequenceLoop() {
  if (state.sequenceExportActive) {
    stopLayerSequenceLoop();
    return;
  }
  const activeStrokes = getActiveSequenceStrokes();
  state.sequenceActiveStrokeIds = new Set(activeStrokes.map((stroke) => stroke.id));
  if (!activeStrokes.length) {
    stopLayerSequenceLoop();
    return;
  }
  startLayerSequenceLoop();
}

function renderEditLayers() {
  if (!editLayerList || state.sidebarTab !== "edit") {
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
    name.title = "Double-click to rename";
    name.dataset.layerAction = "rename";

    const sequenceButton = document.createElement("button");
    sequenceButton.type = "button";
    sequenceButton.className = "edit-layer-sequence-button";
    sequenceButton.dataset.layerAction = "sequence";
    sequenceButton.title = stroke.sequenceOpen ? "Hide effects controls" : "Show effects controls";
    sequenceButton.setAttribute("aria-label", sequenceButton.title);
    sequenceButton.setAttribute("aria-expanded", String(Boolean(stroke.sequenceOpen)));
    sequenceButton.setAttribute("aria-pressed", String(Boolean(stroke.sequenceOpen)));
    const sequenceIcon = document.createElement("span");
    sequenceIcon.className = "edit-layer-sequence-symbol";
    sequenceIcon.setAttribute("aria-hidden", "true");
    sequenceButton.appendChild(sequenceIcon);

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
    row.appendChild(eyeButton);

    entry.appendChild(row);
    if (stroke.sequenceOpen) {
      entry.appendChild(createLayerBlendModeControl(stroke));
      entry.appendChild(createLayerPropertyControls(stroke));
      const slotCount = getLayerSequenceSlotCount(stroke);
      if (slotCount <= 0) {
        const addRow = createLayerSequenceAddRemoveRow(stroke, -1, 0);
        if (addRow) {
          entry.appendChild(addRow);
        }
      }
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
          enabledButton.textContent = isLayerSequenceEnabled(stroke) ? "👁" : "○";
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
  renderLayerSequencePreviews(performance.now(), { force: true });
}

function reflowStrokeDomOrder(save = true) {
  invalidateStampOcclusion();
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
  if (save) {
    scheduleSessionSave();
  }
  syncSceneRendererOrder();
  scheduleStampOcclusionRefresh();
}

function moveStrokeToVisualIndex(stroke, visualIndex, options = {}) {
  const currentIndex = state.strokes.indexOf(stroke);
  if (currentIndex < 0) {
    return false;
  }

  const render = options.render !== false;
  const save = options.save !== false;
  state.strokes.splice(currentIndex, 1);
  const targetStateIndex = Math.max(
    0,
    Math.min(state.strokes.length, state.strokes.length - Math.max(0, visualIndex))
  );
  state.strokes.splice(targetStateIndex, 0, stroke);
  reflowStrokeDomOrder(save);
  if (render) {
    renderEditLayers();
  }
  return true;
}

function getEditLayerEntries() {
  if (!editLayerList) {
    return [];
  }
  return Array.from(editLayerList.querySelectorAll(".edit-layer-entry"));
}

function getEditLayerVisualIndexAt(clientY) {
  if (!editLayerList) {
    return -1;
  }

  const entries = getEditLayerEntries();
  if (!entries.length) {
    return -1;
  }

  for (let index = 0; index < entries.length; index += 1) {
    const row = entries[index].querySelector(".edit-layer-row");
    const rect = (row || entries[index]).getBoundingClientRect();
    if (clientY < rect.top + rect.height / 2) {
      return index;
    }
  }
  return entries.length - 1;
}

function moveEditLayerEntryToVisualIndex(entry, visualIndex) {
  if (!editLayerList || !entry) {
    return;
  }
  const entries = getEditLayerEntries().filter((candidate) => candidate !== entry);
  const targetIndex = clamp(Math.round(Number(visualIndex)) || 0, 0, entries.length);
  const beforeNode = entries[targetIndex] || null;
  editLayerList.insertBefore(entry, beforeNode);
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
  const entry = row.closest(".edit-layer-entry");
  const visualIndex = getEditLayerEntries().indexOf(entry);
  state.editLayerDrag = {
    pointerId: event.pointerId,
    stroke,
    entry,
    row,
    startY: event.clientY,
    targetVisualIndex: visualIndex >= 0 ? visualIndex : getEditLayerVisualIndexAt(event.clientY),
    dragging: false,
    overDelete: false
  };
  try {
    row.setPointerCapture(event.pointerId);
    state.editLayerDrag.captureElement = row;
  } catch (error) {
    // Pointer capture can fail if the pointer ended before the browser processed it.
  }
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
    setEditLayerDeleteDropzoneState(false, false);
    return;
  }
  if (drag.entry) {
    drag.entry.classList.add("is-layer-dragging");
  }

  updateEditLayerDeleteDropzonePosition();
  drag.overDelete = isPointerOverEditLayerDeleteDropzone(event);
  setEditLayerDeleteDropzoneState(true, drag.overDelete);
  if (drag.overDelete) {
    return;
  }

  const visualIndex = getEditLayerVisualIndexAt(event.clientY);
  if (visualIndex >= 0 && visualIndex !== drag.targetVisualIndex) {
    drag.targetVisualIndex = visualIndex;
    moveEditLayerEntryToVisualIndex(drag.entry, visualIndex);
    moveStrokeToVisualIndex(drag.stroke, visualIndex, { render: false, save: false });
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
  if (
    drag.captureElement &&
    typeof drag.captureElement.hasPointerCapture === "function" &&
    drag.captureElement.hasPointerCapture(pointerId)
  ) {
    drag.captureElement.releasePointerCapture(pointerId);
  }
  if (drag.entry) {
    drag.entry.classList.remove("is-layer-dragging");
  }
  if (drag.row) {
    drag.row.classList.remove("is-dragging");
  }
  state.editLayerDrag = null;
  setEditLayerDeleteDropzoneState(false, false);
  if (shouldDelete && pushLayerDeleteAction(drag.stroke)) {
    return;
  }
  if (drag.dragging && Number.isFinite(Number(drag.targetVisualIndex))) {
    moveStrokeToVisualIndex(drag.stroke, Number(drag.targetVisualIndex), { render: false, save: true });
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

const stampHitTestCanvas = document.createElement("canvas");
stampHitTestCanvas.width = 1;
stampHitTestCanvas.height = 1;
const stampHitTestContext = stampHitTestCanvas.getContext("2d", { alpha: true, willReadFrequently: true });

function parseTransformOriginComponent(value, size) {
  const text = String(value || "").trim();
  if (text.endsWith("%")) {
    return (parseFloat(text) / 100) * size;
  }
  const numericValue = parseFloat(text);
  return Number.isFinite(numericValue) ? numericValue : size / 2;
}

function getStampLocalPointFromClient(element, clientX, clientY) {
  if (!(element instanceof HTMLImageElement)) {
    return null;
  }
  const width = Math.max(0, parseFloat(element.style.width) || element.width || 0);
  const height = Math.max(0, parseFloat(element.style.height) || element.height || 0);
  if (width <= 0 || height <= 0) {
    return null;
  }

  const worldPoint = screenToWorld(clientX, clientY);
  const left = parseFloat(element.style.left) || 0;
  const top = parseFloat(element.style.top) || 0;
  const style = window.getComputedStyle(element);
  const originParts = String(style.transformOrigin || "50% 50%").split(/\s+/);
  const originX = parseTransformOriginComponent(originParts[0], width);
  const originY = parseTransformOriginComponent(originParts[1], height);

  try {
    const matrix = new DOMMatrix(style.transform && style.transform !== "none" ? style.transform : undefined);
    const inverse = matrix.inverse();
    const transformedPoint = new DOMPoint(
      worldPoint.x - left - originX,
      worldPoint.y - top - originY
    ).matrixTransform(inverse);
    const localX = transformedPoint.x + originX;
    const localY = transformedPoint.y + originY;
    return { x: localX, y: localY, width, height };
  } catch (error) {
    return {
      x: worldPoint.x - left,
      y: worldPoint.y - top,
      width,
      height
    };
  }
}

function isStampPixelOpaqueAtClientPoint(element, clientX, clientY) {
  if (
    !(element instanceof HTMLImageElement) ||
    !element.classList.contains("stamp") ||
    element.classList.contains("is-layer-hidden") ||
    element.classList.contains("is-culled")
  ) {
    return false;
  }

  const localPoint = getStampLocalPointFromClient(element, clientX, clientY);
  if (
    !localPoint ||
    localPoint.x < 0 ||
    localPoint.y < 0 ||
    localPoint.x > localPoint.width ||
    localPoint.y > localPoint.height
  ) {
    return false;
  }

  if (!stampHitTestContext || !element.complete || !element.naturalWidth || !element.naturalHeight) {
    return true;
  }

  const sourceX = clamp(Math.floor((localPoint.x / localPoint.width) * element.naturalWidth), 0, element.naturalWidth - 1);
  const sourceY = clamp(Math.floor((localPoint.y / localPoint.height) * element.naturalHeight), 0, element.naturalHeight - 1);
  try {
    stampHitTestContext.clearRect(0, 0, 1, 1);
    stampHitTestContext.drawImage(element, sourceX, sourceY, 1, 1, 0, 0, 1, 1);
    return stampHitTestContext.getImageData(0, 0, 1, 1).data[3] > 8;
  } catch (error) {
    return true;
  }
}

function getBufferedHitTestOffsets(radiusPx) {
  const radius = Math.max(0, Math.round(Number(radiusPx) || 0));
  const offsets = [{ x: 0, y: 0, distanceSquared: 0 }];
  for (let y = -radius; y <= radius; y += 1) {
    for (let x = -radius; x <= radius; x += 1) {
      if (x === 0 && y === 0) {
        continue;
      }
      const distanceSquared = x * x + y * y;
      if (distanceSquared <= radius * radius) {
        offsets.push({ x, y, distanceSquared });
      }
    }
  }
  offsets.sort((left, right) => left.distanceSquared - right.distanceSquared);
  return offsets;
}

function getTopOpaqueStampFromSpatialIndex(clientX, clientY) {
  const worldPoint = screenToWorld(clientX, clientY);
  const radiusWorld = Math.max(
    EDIT_LAYER_OPAQUE_HIT_BUFFER_PX / Math.max(0.0001, state.camera.scale),
    1
  );
  const candidates = Array.from(getEraseCandidateStamps(worldPoint.x, worldPoint.y, radiusWorld));
  if (!candidates.length) {
    return null;
  }

  const worldOrder = new Map();
  const stamps = world.getElementsByClassName("stamp");
  for (let index = 0; index < stamps.length; index += 1) {
    worldOrder.set(stamps[index], index);
  }

  candidates.sort((left, right) => (worldOrder.get(right) || 0) - (worldOrder.get(left) || 0));
  const offsets = getBufferedHitTestOffsets(EDIT_LAYER_OPAQUE_HIT_BUFFER_PX);
  for (const stamp of candidates) {
    if (!(stamp instanceof HTMLImageElement) || stamp.parentElement !== world) {
      continue;
    }
    for (const offset of offsets) {
      if (isStampPixelOpaqueAtClientPoint(stamp, clientX + offset.x, clientY + offset.y)) {
        return stamp;
      }
    }
  }
  return null;
}

function getTopOpaqueStampAtClientPoint(clientX, clientY, options = {}) {
  const offsets = getBufferedHitTestOffsets(EDIT_LAYER_OPAQUE_HIT_BUFFER_PX);
  for (const offset of offsets) {
    const sampleX = clientX + offset.x;
    const sampleY = clientY + offset.y;
    const elements = document.elementsFromPoint(sampleX, sampleY);
    for (const element of elements) {
      const stamp = element instanceof Element ? element.closest(".stamp") : null;
      if (!(stamp instanceof HTMLImageElement) || stamp.parentElement !== world) {
        continue;
      }
      if (isStampPixelOpaqueAtClientPoint(stamp, sampleX, sampleY)) {
        return stamp;
      }
    }
  }
  if (options.includePointerTransparent) {
    return getTopOpaqueStampFromSpatialIndex(clientX, clientY);
  }
  return null;
}

function updateEditLayerHoverCursor(clientX = state.lastPointerClientX, clientY = state.lastPointerClientY) {
  if (
    state.sidebarTab !== "edit" ||
    state.exportMode ||
    state.placementTask ||
    state.editLayerMove ||
    state.panning ||
    state.touchGesture ||
    !state.pointerInViewport ||
    !Number.isFinite(clientX) ||
    !Number.isFinite(clientY)
  ) {
    viewport.classList.remove("is-edit-layer-clickable");
    return;
  }

  const stamp = getTopOpaqueStampAtClientPoint(clientX, clientY);
  const stroke = getStampLayerStroke(stamp);
  viewport.classList.toggle("is-edit-layer-clickable", Boolean(stamp && stroke && !stroke.hidden));
}

function setStampWorldPosition(element, left, top, options = {}) {
  element.style.left = `${left}px`;
  element.style.top = `${top}px`;
  delete element.dataset.worldLeft;
  delete element.dataset.worldTop;
  delete element.dataset.worldRight;
  delete element.dataset.worldBottom;
  if (options.markDirty !== false) {
    markStrokeSerializationDirty(getStampLayerStroke(element));
  }
}

function createLayerMoveHistoryAction(move, dx, dy) {
  if (!move?.stroke || !Array.isArray(move.originals) || (!dx && !dy)) {
    return null;
  }
  const elements = [];
  const beforePositions = new Float64Array(move.originals.length * 2);
  for (let index = 0; index < move.originals.length; index += 1) {
    const original = move.originals[index];
    elements.push(original.element);
    beforePositions[index * 2] = original.left;
    beforePositions[index * 2 + 1] = original.top;
  }
  return {
    type: "layer-move",
    keyboardOnly: true,
    stroke: move.stroke,
    elements,
    beforePositions,
    dx,
    dy
  };
}

function applyLayerMoveHistoryAction(action, useAfterPositions) {
  if (
    !action?.stroke ||
    !Array.isArray(action.elements) ||
    !(action.beforePositions instanceof Float64Array) ||
    action.beforePositions.length !== action.elements.length * 2
  ) {
    return false;
  }

  invalidateStampOcclusion();
  const viewportBounds = getViewportVisibilityBounds();
  for (const element of action.elements) {
    if (element instanceof HTMLImageElement && element.parentElement === world) {
      unregisterStampSpatialCells(element);
    }
  }
  const offsetX = useAfterPositions ? Number(action.dx) || 0 : 0;
  const offsetY = useAfterPositions ? Number(action.dy) || 0 : 0;
  for (let index = 0; index < action.elements.length; index += 1) {
    const element = action.elements[index];
    if (!(element instanceof HTMLImageElement)) {
      continue;
    }
    setStampWorldPosition(
      element,
      action.beforePositions[index * 2] + offsetX,
      action.beforePositions[index * 2 + 1] + offsetY,
      { markDirty: false }
    );
  }
  markStrokeSerializationDirty(action.stroke);
  for (const element of action.elements) {
    if (
      element instanceof HTMLImageElement &&
      !action.stroke.hidden &&
      element.parentElement === world
    ) {
      registerStampSpatialCells(element);
      updateStampViewportVisibility(element, viewportBounds);
    }
  }
  syncSceneRendererElements(action.elements);
  scheduleStampVisibilityRefresh();
  scheduleStampOcclusionRefresh();
  return true;
}

function startEditLayerMove(event) {
  if (state.sidebarTab !== "edit") {
    return false;
  }

  const stamp = getTopOpaqueStampAtClientPoint(event.clientX, event.clientY);
  const stroke = getStampLayerStroke(stamp);
  if (!stroke || stroke.hidden) {
    return false;
  }

  invalidateStampOcclusion();

  event.preventDefault();
  hideBrushCursorPreview();
  viewport.classList.remove("is-edit-layer-clickable");
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
  let changed = false;
  for (const original of move.originals) {
    if (!move.liveSet.has(original.element)) {
      continue;
    }
    setStampWorldPosition(
      original.element,
      original.left + move.dx,
      original.top + move.dy,
      { markDirty: false }
    );
    changed = true;
  }
  if (changed) {
    markStrokeSerializationDirty(move.stroke);
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

  const dx = Math.abs(Number(move.dx) || 0) > 0.001 ? Number(move.dx) : 0;
  const dy = Math.abs(Number(move.dy) || 0) > 0.001 ? Number(move.dy) : 0;
  const historyAction = createLayerMoveHistoryAction(move, dx, dy);
  const viewportBounds = getViewportVisibilityBounds();
  for (const original of move.originals) {
    unregisterStampSpatialCells(original.element);
    setStampWorldPosition(
      original.element,
      original.left + dx,
      original.top + dy,
      { markDirty: false }
    );
  }
  if (historyAction) {
    markStrokeSerializationDirty(move.stroke);
  }
  for (const original of move.originals) {
    if (!move.stroke.hidden && original.element.parentElement === world) {
      registerStampSpatialCells(original.element);
      updateStampViewportVisibility(original.element, viewportBounds);
    }
  }

  state.editLayerMove = null;
  updateEditLayerHoverCursor();
  scheduleStampVisibilityRefresh();
  if (historyAction) {
    syncSceneRendererElements(historyAction.elements);
    pushLayerMoveHistoryAction(historyAction);
  }
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
      if (!(state.selectedBrushIds instanceof Set)) {
        state.selectedBrushIds = new Set();
      }
      const currentSoloBrushId = Number(state.soloBrushId);
      if (
        Number.isFinite(currentSoloBrushId) &&
        currentSoloBrushId !== previewBrush.id &&
        findBrushById(currentSoloBrushId)
      ) {
        state.selectedBrushIds.add(currentSoloBrushId);
      }
      state.soloBrushId = null;
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
  const source = getCanonicalStockBrushSource(
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
  state.sceneRendererLastCameraChangeAt = performance.now();
  if (sceneRendererCameraIdleTimerId !== null) {
    window.clearTimeout(sceneRendererCameraIdleTimerId);
  }
  sceneRendererCameraIdleTimerId = window.setTimeout(() => {
    sceneRendererCameraIdleTimerId = null;
    scheduleSceneRendererEvaluation();
  }, 180);
  setInlineStyleIfChanged(
    world,
    "transform",
    `translate(${state.camera.x}px, ${state.camera.y}px) scale(${state.camera.scale})`
  );
  if (state.sceneRendererPreparing) {
    noteSceneRendererMutation();
  }
  syncSceneRendererCamera();
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
  invalidateStampOcclusion();
  removeSceneRendererElements(stroke.elements);
  for (const element of stroke.elements) {
    unregisterStampSpatialCells(element);
    state.viewportRenderedStamps.delete(element);
    decrementUrlRef(element.dataset.brushUrl);
    if (element.parentElement === world) {
      removeSequencePixelateProxy(element);
      element.remove();
      state.stampCount = Math.max(0, state.stampCount - 1);
    }
  }
  scheduleStampVisibilityRefresh();
  refreshLayerSequenceLoop();
}

function appendStrokeToWorld(stroke) {
  const viewportBounds = getViewportVisibilityBounds();
  const hidden = Boolean(stroke.hidden);
  applyStrokeBlendMode(stroke);
  for (const element of stroke.elements) {
    if (element.parentElement !== world) {
      state.stampCount += 1;
    }
    world.appendChild(element);
    if (!state.sceneRendererActive) {
      restoreSceneRendererStamp(element);
    }
    element.classList.toggle("is-layer-hidden", hidden);
    if (!hidden) {
      registerStampSpatialCells(element);
      updateStampViewportVisibility(element, viewportBounds);
    }
    applyGifPauseStateToImage(element);
    incrementUrlRef(element.dataset.brushUrl);
  }
  applyStrokeLayerVisuals(stroke);
  scheduleStampVisibilityRefresh();
  scheduleStampOcclusionRefresh();
  refreshLayerSequenceLoop();
  scheduleSceneRendererFullSync();
}

function markKeyboardHistoryActionPerformed(action) {
  if (!action || typeof action !== "object") {
    return;
  }
  action.keyboardHistoryOrder = state.nextKeyboardHistoryOrder;
  state.nextKeyboardHistoryOrder += 1;
  delete action.keyboardUndoOrder;
}

function markKeyboardHistoryActionUndone(action) {
  if (!action || typeof action !== "object") {
    return;
  }
  action.keyboardUndoOrder = state.nextKeyboardUndoOrder;
  state.nextKeyboardUndoOrder += 1;
}

function clearLayerMoveHistory() {
  state.layerMoveHistory = [];
  state.layerMoveRedoHistory = [];
}

function resetKeyboardHistoryTracking() {
  clearLayerMoveHistory();
  resetExportCropHistory();
  state.nextKeyboardHistoryOrder = 1;
  state.nextKeyboardUndoOrder = 1;
}

function finishLayerMoveHistoryChange() {
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
  scheduleStampOcclusionRefresh();
  scheduleSceneRendererEvaluation();
}

function pushLayerMoveHistoryAction(action) {
  if (!action || action.type !== "layer-move") {
    return false;
  }
  state.redoHistory = [];
  state.layerMoveRedoHistory = [];
  markKeyboardHistoryActionPerformed(action);
  state.layerMoveHistory.push(action);
  if (state.layerMoveHistory.length > LAYER_MOVE_HISTORY_LIMIT) {
    state.layerMoveHistory.splice(
      0,
      state.layerMoveHistory.length - LAYER_MOVE_HISTORY_LIMIT
    );
  }
  finishLayerMoveHistoryChange();
  return true;
}

function undoLastLayerMove() {
  const action = state.layerMoveHistory[state.layerMoveHistory.length - 1];
  if (!action || !applyLayerMoveHistoryAction(action, false)) {
    return false;
  }
  state.layerMoveHistory.pop();
  markKeyboardHistoryActionUndone(action);
  state.layerMoveRedoHistory.push(action);
  finishLayerMoveHistoryChange();
  return true;
}

function redoLastLayerMove() {
  const action = state.layerMoveRedoHistory[state.layerMoveRedoHistory.length - 1];
  if (!action || !applyLayerMoveHistoryAction(action, true)) {
    return false;
  }
  state.layerMoveRedoHistory.pop();
  markKeyboardHistoryActionPerformed(action);
  state.layerMoveHistory.push(action);
  finishLayerMoveHistoryChange();
  return true;
}

function getLastHistoryAction(history) {
  return Array.isArray(history) && history.length ? history[history.length - 1] : null;
}

function undoKeyboardHistoryAction() {
  const sceneAction = getLastHistoryAction(state.history);
  const layerAction = getLastHistoryAction(state.layerMoveHistory);
  const sceneOrder = Number(sceneAction?.keyboardHistoryOrder) || 0;
  const layerOrder = Number(layerAction?.keyboardHistoryOrder) || 0;
  return layerOrder > sceneOrder ? undoLastLayerMove() : undoLastStroke();
}

function redoKeyboardHistoryAction() {
  const sceneAction = getLastHistoryAction(state.redoHistory);
  const layerAction = getLastHistoryAction(state.layerMoveRedoHistory);
  const sceneOrder = Number(sceneAction?.keyboardUndoOrder) || 0;
  const layerOrder = Number(layerAction?.keyboardUndoOrder) || 0;
  return layerOrder > sceneOrder ? redoLastLayerMove() : redoLastStroke();
}

function pushHistoryAction(action) {
  state.redoHistory = [];
  state.layerMoveRedoHistory = [];
  markKeyboardHistoryActionPerformed(action);
  state.history.push(action);
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
  scheduleStampOcclusionRefresh();
  scheduleSceneRendererEvaluation();
}

function pushStroke(stroke) {
  if (!stroke.elements.length) {
    return;
  }

  applyStrokeBlendMode(stroke);
  applyStrokeLayerVisuals(stroke);
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
  if (state.sceneRendererActive || state.sceneRendererPreparing) {
    // Restored stamps can return at arbitrary z positions. Use the DOM renderer
    // for this interaction so no temporary hybrid ordering can be visible.
    deactivateSceneRenderer();
  }
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
  const currentWorldStampOrder = getSceneRendererStampsInOrder();
  const restoredStrokes = new Set();

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
      markStrokeSerializationDirty(stroke);
      removal.element.dataset.strokeId = String(stroke.id);
      restoredStrokes.add(stroke);
    }

    if (removal.element.parentElement !== world) {
      const preferredWorldIndex =
        Number.isFinite(Number(removal.worldIndex)) && Number(removal.worldIndex) >= 0
        ? Number(removal.worldIndex)
        : currentWorldStampOrder.length;
      const insertWorldIndex = Math.max(0, Math.min(preferredWorldIndex, currentWorldStampOrder.length));
      const beforeNode = currentWorldStampOrder[insertWorldIndex] || null;
      world.insertBefore(removal.element, beforeNode);
      currentWorldStampOrder.splice(insertWorldIndex, 0, removal.element);
      if (!state.sceneRendererActive) {
        restoreSceneRendererStamp(removal.element);
      }
      state.stampCount += 1;
      registerStampSpatialCells(removal.element);
      updateStampViewportVisibility(removal.element);
      applyGifPauseStateToImage(removal.element);
      incrementUrlRef(removal.element.dataset.brushUrl);
      syncSceneRendererElements([removal.element]);
    }
  }
  for (const stroke of restoredStrokes) {
    invalidateStrokeSequenceTopology(stroke);
  }
  scheduleStampVisibilityRefresh();
  refreshLayerSequenceLoop();
  scheduleStampOcclusionRefresh();
  syncSceneRendererOrder();
}

function redoEraseAction(action) {
  const removals = Array.isArray(action.removals) ? action.removals : [];
  for (const removal of removals) {
    if (!removal || !removal.element) {
      continue;
    }
    removeStampElementFromState(removal.element);
  }
  scheduleStampOcclusionRefresh();
  scheduleSceneRendererEvaluation();
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
    return false;
  }

  if (action.type === "draw") {
    undoDrawAction(action);
  } else if (action.type === "erase") {
    undoEraseAction(action);
  } else if (action.type === "layer-delete") {
    undoLayerDeleteAction(action);
  } else {
    state.history.push(action);
    return false;
  }

  markKeyboardHistoryActionUndone(action);
  state.redoHistory.push(action);
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
  scheduleStampOcclusionRefresh();
  scheduleSceneRendererEvaluation();
  return true;
}

function redoLastStroke() {
  const action = state.redoHistory[state.redoHistory.length - 1];
  if (!action) {
    return false;
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
    return false;
  }

  state.redoHistory.pop();
  markKeyboardHistoryActionPerformed(action);
  state.history.push(action);
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
  scheduleStampOcclusionRefresh();
  scheduleSceneRendererEvaluation();
  return true;
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
  resetKeyboardHistoryTracking();
  clearCursorTrail();
  updateUndoState();
  updateBrushStatus();
  renderEditLayers();
  scheduleSessionSave();
  scheduleStampOcclusionRefresh();
  scheduleSceneRendererEvaluation();
}

function getBrushWeight(brush) {
  const mode = normalizeBrushWeightMode(brush?.weightMode);
  return BRUSH_WEIGHT_MULTIPLIERS[mode] || 1;
}

function getBrushChoicePool() {
  if (
    brushChoicePoolCache &&
    brushChoicePoolCache.revision === brushChoiceCacheRevision &&
    brushChoicePoolCache.brushesSource === state.brushes &&
    brushChoicePoolCache.selectedSource === state.selectedBrushIds &&
    brushChoicePoolCache.soloBrushId === state.soloBrushId
  ) {
    return brushChoicePoolCache;
  }

  const selectedBrushes = getSelectedBrushes();
  const candidates = selectedBrushes.length
    ? selectedBrushes
    : state.brushes.filter((brush) => brush.enabled);
  const cumulativeWeights = new Float64Array(candidates.length);
  let totalWeight = 0;
  for (let index = 0; index < candidates.length; index += 1) {
    totalWeight += getBrushWeight(candidates[index]);
    cumulativeWeights[index] = totalWeight;
  }
  brushChoicePoolCache = {
    revision: brushChoiceCacheRevision,
    brushesSource: state.brushes,
    selectedSource: state.selectedBrushIds,
    soloBrushId: state.soloBrushId,
    candidates,
    cumulativeWeights,
    totalWeight
  };
  return brushChoicePoolCache;
}

function pickRandomBrush() {
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    return soloBrush;
  }

  const { candidates, cumulativeWeights, totalWeight } = getBrushChoicePool();
  if (!candidates.length) {
    return null;
  }

  const randomWeight = Math.random() * totalWeight;
  let low = 0;
  let high = cumulativeWeights.length - 1;
  while (low < high) {
    const middle = (low + high) >> 1;
    if (randomWeight <= cumulativeWeights[middle]) {
      high = middle;
    } else {
      low = middle + 1;
    }
  }
  return candidates[low] || candidates[candidates.length - 1];
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

  const { width, height } = getBrushPlacementSize(brush, { randomize: true });
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
  stamp.dataset.sequenceDisplayedSource = brush.url;
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
  markStrokeSerializationDirty(stroke);
  scheduleSceneRendererElementsSync([stamp]);
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

async function placeRectOutlineBrushes(stroke, startX, startY, endX, endY, task = null) {
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

  for (let yIndex = 0; yIndex < yPositions.length; yIndex += 1) {
    const y = yPositions[yIndex];
    const isEdgeY = yIndex === 0 || yIndex === yPositions.length - 1;
    for (let xIndex = 0; xIndex < xPositions.length; xIndex += 1) {
      const isEdgeX = xIndex === 0 || xIndex === xPositions.length - 1;
      if (!isEdgeX && !isEdgeY) {
        continue;
      }
      throwIfTaskCancelled(task);
      if (stroke.elements.length >= capacity) {
        return placedAny;
      }
      if (!placeBrush(xPositions[xIndex], y, stroke)) {
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

async function placeCircleOutlineBrushes(stroke, startX, startY, endX, endY, task = null) {
  const bounds = getCircleBoundsFromPoints(startX, startY, endX, endY);
  const spacing = getSpacingValue();
  const xPositions = getGridAxisPositions(bounds.left, bounds.right, spacing);
  const yPositions = getGridAxisPositions(bounds.top, bounds.bottom, spacing);
  const centerX = (bounds.left + bounds.right) / 2;
  const centerY = (bounds.top + bounds.bottom) / 2;
  const radius = Math.max(0, (bounds.right - bounds.left) / 2);
  const radiusSq = radius * radius;
  const innerRadius = Math.max(0, radius - spacing);
  const innerRadiusSq = innerRadius * innerRadius;
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
      const distanceSq = dx * dx + dy * dy;
      if (distanceSq > radiusSq || distanceSq < innerRadiusSq) {
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
  const baseMode = getBaseDrawMode(mode);
  if (baseMode === "line") {
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

  if (baseMode === "box") {
    setShapePreviewBox(getRectBoundsFromPoints(startX, startY, endX, endY), "is-box");
    return;
  }

  if (baseMode === "circle") {
    setShapePreviewBox(getCircleBoundsFromPoints(startX, startY, endX, endY), "is-circle");
  }
}

async function commitShapeStroke(mode, startX, startY, endX, endY) {
  if (state.placementTask) {
    return false;
  }

  const baseMode = getBaseDrawMode(mode);
  const isOutlineMode = isOutlineShapeDrawMode(mode);
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
    if (baseMode === "line") {
      await placeLineBrushes(stroke, startX, startY, endX, endY, task);
    } else if (baseMode === "box") {
      if (isOutlineMode) {
        await placeRectOutlineBrushes(stroke, startX, startY, endX, endY, task);
      } else {
        await placeRectBrushes(stroke, startX, startY, endX, endY, task);
      }
    } else if (baseMode === "circle") {
      if (isOutlineMode) {
        await placeCircleOutlineBrushes(stroke, startX, startY, endX, endY, task);
      } else {
        await placeCircleBrushes(stroke, startX, startY, endX, endY, task);
      }
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
    scheduleSceneRendererEvaluation();
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
  markStrokeSerializationDirty(state.drawing.stroke);
  registerStampSpatialCells(tail);
  scheduleSceneRendererElementsSync([tail]);
}

function rectsIntersect(a, b) {
  return !(a.right <= b.left || a.left >= b.right || a.bottom <= b.top || a.top >= b.bottom);
}

function getExportSequenceVisualState(element, now = performance.now()) {
  const stroke = getStampLayerStroke(element);
  const baseOpacity = stroke
    ? getLayerOpacityFraction(stroke)
    : clamp(Number(element.dataset.sequenceBaseOpacity) || Number(element.style.opacity) || 1, 0, 1);
  const currentSource = element.getAttribute("src") || element.currentSrc || "";
  const baseSource = element.dataset.brushUrl || currentSource;
  const visual = {
    opacity: baseOpacity,
    move: { x: 0, y: 0 },
    rotationOffset: 0,
    scale: 1,
    groupedTransform: null,
    tintSettings: getStampBaseTintSettings(element),
    pixelateAmount: 0,
    blurAmount: 0,
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
    if (slot.timingStyle === "grouped" && isGroupedLayerSequenceEffect(effect)) {
      const runtime = Array.isArray(stroke.sequenceSlotRuntimes)
        ? stroke.sequenceSlotRuntimes[slotIndex]
        : null;
      const groupStamp = {
        dataset: runtime?.groupDataset && typeof runtime.groupDataset === "object"
          ? { ...runtime.groupDataset }
          : {}
      };
      applyGroupedSequenceEffectToVisual(visual, effect, groupStamp, settings, now);
      continue;
    }
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
    } else if (effect === "pixelate") {
      visual.pixelateAmount = Math.max(
        visual.pixelateAmount,
        Math.round(getCurrentSequencePixelateAmount(element, settings, now))
      );
    } else if (effect === "blur") {
      visual.blurAmount += getCurrentSequenceBlurAmount(element, settings, now);
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

function createExportStampEntry(element, selectionBounds, sequenceNow = null, options = {}) {
  const stroke = getStampLayerStroke(element);
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
  const rotation = (Number(element.dataset.rotation) || 0) + (Number(sequenceState?.rotationOffset) || 0);
  const moveX = Number(sequenceState?.move?.x) || 0;
  const moveY = Number(sequenceState?.move?.y) || 0;
  const layerTransform = sequenceState?.groupedTransform
    ? getStampGroupedLayerTransform(stroke, element, sequenceState.groupedTransform)
    : getStampLayerTransform(stroke, element);
  const totalScale = visualScale * layerTransform.scale;
  const totalWidth = width * totalScale;
  const totalHeight = height * totalScale;
  const totalRotation = rotation + layerTransform.rotation;
  const centerX = left + width / 2 + layerTransform.x + moveX;
  const centerY = top + height / 2 + layerTransform.y + moveY;
  const bounds = getStampWorldBoundsFromLayout(
    centerX - totalWidth / 2,
    centerY - totalHeight / 2,
    totalWidth,
    totalHeight,
    totalRotation
  );
  const isInSelection = rectsIntersect(bounds, selectionBounds);
  const sequenceCandidate = Boolean(
    options.includeSequenceCandidates === true &&
    stroke &&
    isLayerSequenceEnabled(stroke)
  );
  if (!isInSelection && !sequenceCandidate) {
    return null;
  }

  return {
    element,
    isInSelection,
    sequenceCandidate,
    sourceUrl: sequenceState?.sourceUrl || element.dataset.brushUrl || element.currentSrc || element.getAttribute("src") || "",
    centerX,
    centerY,
    width: totalWidth,
    height: totalHeight,
    rotation: totalRotation,
    opacity: sequenceState ? sequenceState.opacity : clamp(Number(element.style.opacity) || 1, 0, 1),
    strokeId: stroke && Number.isFinite(Number(stroke.id)) ? Number(stroke.id) : null,
    blendMode: getLayerBlendMode(stroke),
    tintSettings: sequenceState?.tintSettings || getStampBaseTintSettings(element),
    pixelateAmount: Number(sequenceState?.pixelateAmount) || 0,
    blurAmount: Number(sequenceState?.blurAmount) || 0,
    imageRendering: Number(sequenceState?.pixelateAmount) > 0
      ? "pixelated"
      : element.style.imageRendering === "auto"
      ? "auto"
      : "pixelated"
  };
}

async function collectExportStampEntries(selectionBounds, task = null, progress = null, options = {}) {
  const entries = [];
  const stamps = getVisibleStampElements();
  const total = Math.max(1, stamps.length);

  for (let index = 0; index < stamps.length; index += 1) {
    throwIfTaskCancelled(task);
    const entry = createExportStampEntry(stamps[index], selectionBounds, null, options);
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
    if (!entry?.sequenceCandidate) {
      continue;
    }
    const nextEntry = createExportStampEntry(
      entry.element,
      selectionBounds,
      sequenceNow,
      { includeSequenceCandidates: true }
    );
    if (nextEntry) {
      nextEntry.imageElement = entry.sourceUrl === nextEntry.sourceUrl ? entry.imageElement : null;
      Object.assign(entry, nextEntry);
    } else {
      entry.isInSelection = false;
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

function getGifLogicalBackgroundColor(parsed) {
  const imageFrames = Array.isArray(parsed?.frames)
    ? parsed.frames.filter((frame) => frame?.image)
    : [];
  const hasTransparentFrames = imageFrames.some(
    (frame) => frame?.gce?.extras?.transparentColorGiven === true
  );
  if (hasTransparentFrames || !Array.isArray(parsed?.gct)) {
    return "";
  }
  const backgroundIndex = Number(parsed?.lsd?.backgroundColorIndex);
  const color = Number.isInteger(backgroundIndex) ? parsed.gct[backgroundIndex] : null;
  if (!Array.isArray(color) || color.length < 3) {
    return "";
  }
  const red = clamp(Math.round(Number(color[0]) || 0), 0, 255);
  const green = clamp(Math.round(Number(color[1]) || 0), 0, 255);
  const blue = clamp(Math.round(Number(color[2]) || 0), 0, 255);
  return `rgb(${red}, ${green}, ${blue})`;
}

async function decodeGifAnimation(url) {
  const bytes = await readImageBytes(url);
  const gifuctModule = await loadGifuctModule();
  const parseInput = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
  const parsed = gifuctModule.parseGIF(parseInput);
  const decodedFrames = gifuctModule.decompressFrames(parsed, true);
  const logicalBackgroundColor = getGifLogicalBackgroundColor(parsed);

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
  if (logicalBackgroundColor) {
    compositeCtx.fillStyle = logicalBackgroundColor;
    compositeCtx.fillRect(0, 0, width, height);
  }

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
      if (logicalBackgroundColor) {
        compositeCtx.fillStyle = logicalBackgroundColor;
        compositeCtx.fillRect(left, top, frameWidth, frameHeight);
      } else {
        compositeCtx.clearRect(left, top, frameWidth, frameHeight);
      }
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

function exportSourceUsesGif(sourceUrl, element = null) {
  sourceUrl = String(sourceUrl || "");
  if (isGifUrl(sourceUrl)) {
    return true;
  }
  const brushId = Number(element?.dataset?.brushId);
  const brush = Number.isFinite(brushId) ? findBrushById(brushId) : null;
  if (brush && getBrushSourceIsGif(brush)) {
    return true;
  }
  return state.brushes.some(
    (candidate) =>
      getBrushSourceIsGif(candidate) &&
      (candidate.url === sourceUrl || candidate.originalUrl === sourceUrl)
  );
}

function exportEntryUsesGif(entry) {
  return exportSourceUsesGif(entry?.sourceUrl, entry?.element);
}

async function buildGifAnimationMap(entries, task = null, progress = null, extraUrls = []) {
  const urls = new Set();
  for (const entry of entries) {
    if (!entry || !exportEntryUsesGif(entry)) {
      continue;
    }
    urls.add(entry.sourceUrl);
  }
  for (const url of extraUrls) {
    if (exportSourceUsesGif(url)) {
      urls.add(url);
    }
  }

  const map = new Map();
  const failures = [];
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
      failures.push({ url, error });
    }
    if (progress) {
      progress((index + 1) / total);
    }
    await yieldToMainThread(task);
  }

  if (failures.length) {
    const error = new Error(
      failures.length === 1
        ? "One GIF could not be decoded for rendering."
        : `${failures.length} GIFs could not be decoded for rendering.`
    );
    error.code = "EXPORT_GIF_DECODE_FAILED";
    error.failedSourceUrls = failures.map((failure) => failure.url);
    throw error;
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

function createExportFrameDelaysForCount(durationMs, frameCount) {
  const duration = Math.max(EXPORT_GIF_FRAME_DELAY_MS, Math.round(Number(durationMs) || EXPORT_GIF_DURATION_MS));
  const maxCountForDuration = Math.max(1, Math.floor(duration / 20));
  const safeFrameCount = clamp(
    Math.round(Number(frameCount) || 1),
    1,
    Math.min(EXPORT_MAX_FRAME_COUNT, maxCountForDuration)
  );
  if (safeFrameCount <= 1) {
    return [duration];
  }

  let remainingDuration = duration;
  const delays = [];
  for (let index = 0; index < safeFrameCount; index += 1) {
    const remainingFrames = safeFrameCount - index;
    const delay = Math.max(20, Math.round(remainingDuration / remainingFrames));
    delays.push(delay);
    remainingDuration -= delay;
  }
  return delays;
}

function normalizeFrameDelays(frameDelays) {
  return Array.isArray(frameDelays)
    ? frameDelays
        .map((delay) => Math.max(20, Math.round(Number(delay) || EXPORT_GIF_FRAME_DELAY_MS)))
        .filter((delay) => delay > 0)
    : [];
}

function getFrameDelaysDuration(frameDelays) {
  return normalizeFrameDelays(frameDelays).reduce((sum, delay) => sum + delay, 0);
}

function getExportGifDurationMs(gifAnimationMap, options = {}) {
  const frameCountOverride = Number(options.frameCountOverride);
  if (Number.isFinite(frameCountOverride) && frameCountOverride > 0) {
    const nativeFrameDelays = getNativeGifFrameDelaysForCount(gifAnimationMap, frameCountOverride);
    if (nativeFrameDelays) {
      return getFrameDelaysDuration(nativeFrameDelays);
    }
    return Math.max(
      EXPORT_GIF_FRAME_DELAY_MS,
      clamp(Math.floor(frameCountOverride), 1, EXPORT_MAX_FRAME_COUNT) * EXPORT_GIF_FRAME_DELAY_MS
    );
  }

  if (options.animationAuto !== false) {
    return Math.max(
      getLongestGifAnimationDuration(gifAnimationMap),
      getBackgroundAnimationDuration(options),
      EXPORT_GIF_DURATION_MS
    );
  }

  const manualSeconds = EXPORT_MANUAL_SECONDS_PRESETS.includes(Number(options.animationSeconds))
    ? Number(options.animationSeconds)
    : 1;
  return Math.max(EXPORT_GIF_FRAME_DELAY_MS, Math.round(manualSeconds * 1000));
}

function getExportGifFrameDelays(gifAnimationMap, options = {}) {
  if (Number.isFinite(Number(options.sizeLimitFrameCount)) && Number(options.sizeLimitFrameCount) > 0) {
    return createExportFrameDelaysForCount(
      getExportGifDurationMs(gifAnimationMap, options),
      options.sizeLimitFrameCount
    );
  }

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
  if (Number.isFinite(Number(options.videoDurationMs)) && Number(options.videoDurationMs) > 0) {
    return Math.max(100, Math.round(Number(options.videoDurationMs)));
  }
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

function getManualExportVideoDurationMs() {
  const inputValue = exportVideoLengthInput ? String(exportVideoLengthInput.value || "").trim() : "";
  const sourceValue = inputValue === "" ? state.exportVideoSeconds : Number(inputValue);
  const seconds = clamp(Number(sourceValue) || 0, 0, EXPORT_VIDEO_MAX_SECONDS);
  state.exportVideoSeconds = seconds;
  if (exportVideoLengthInput && inputValue !== "" && Number(exportVideoLengthInput.value) !== seconds) {
    exportVideoLengthInput.value = String(seconds);
  }
  return Math.max(100, Math.round(seconds * 1000));
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

function loadExportBackgroundImageElement(url, task = null) {
  if (!url) {
    return Promise.resolve(null);
  }
  if (!exportBackgroundImageCache.has(url)) {
    exportBackgroundImageCache.set(
      url,
      createExportSourceImageLoadPromise(url).catch((error) => {
        exportBackgroundImageCache.delete(url);
        throw error;
      })
    );
  }
  return waitForExportSourcePromise(exportBackgroundImageCache.get(url), task);
}

function createExportSourceImageLoadPromise(url) {
  return new Promise((resolve, reject) => {
    const image = new Image();
    let settled = false;
    const finish = (callback, value) => {
      if (settled) {
        return;
      }
      settled = true;
      window.clearTimeout(timeoutId);
      image.onload = null;
      image.onerror = null;
      callback(value);
    };
    const timeoutId = window.setTimeout(() => {
      const error = new Error("Export source image load timed out.");
      error.code = "EXPORT_SOURCE_LOAD_TIMEOUT";
      finish(reject, error);
      image.removeAttribute("src");
    }, EXPORT_SOURCE_LOAD_TIMEOUT_MS);
    image.onload = () => finish(resolve, image);
    image.onerror = () => finish(reject, new Error("Could not load export source image."));
    image.src = url;
  });
}

function waitForExportSourcePromise(promise, task = null) {
  if (!task) {
    return promise;
  }
  return new Promise((resolve, reject) => {
    let settled = false;
    const finish = (callback, value) => {
      if (settled) {
        return;
      }
      settled = true;
      window.clearInterval(cancelIntervalId);
      callback(value);
    };
    const cancelIntervalId = window.setInterval(() => {
      if (task.cancelled) {
        finish(reject, createCancellationError());
      }
    }, EXPORT_SOURCE_CANCEL_POLL_MS);
    promise.then(
      (value) => finish(resolve, value),
      (error) => finish(reject, error)
    );
    if (task.cancelled) {
      finish(reject, createCancellationError());
    }
  });
}

function loadExportSourceImageElement(url, options = {}) {
  if (!url || url === TRANSPARENT_STAMP_SRC) {
    return Promise.resolve(null);
  }
  if (options.cache === false) {
    return createExportSourceImageLoadPromise(url);
  }
  if (!exportSourceImageCache.has(url)) {
    exportSourceImageCache.set(
      url,
      createExportSourceImageLoadPromise(url).catch((error) => {
        exportSourceImageCache.delete(url);
        throw error;
      })
    );
    while (exportSourceImageCache.size > EXPORT_SOURCE_IMAGE_CACHE_LIMIT) {
      const oldestUrl = exportSourceImageCache.keys().next().value;
      if (!oldestUrl) {
        break;
      }
      exportSourceImageCache.delete(oldestUrl);
    }
  }
  return exportSourceImageCache.get(url);
}

async function loadExportSourceImageElementWithRetry(url, task = null, attempts = 2, options = {}) {
  let lastError = null;
  const attemptCount = Math.max(1, Math.round(Number(attempts) || 1));
  for (let attempt = 0; attempt < attemptCount; attempt += 1) {
    throwIfTaskCancelled(task);
    try {
      return await waitForExportSourcePromise(
        loadExportSourceImageElement(url, options),
        task
      );
    } catch (error) {
      if (isCancellationError(error)) {
        throw error;
      }
      lastError = error;
      if (options.cache !== false) {
        exportSourceImageCache.delete(url);
      }
      if (attempt + 1 < attemptCount) {
        await yieldToMainThread(task);
      }
    }
  }
  throw lastError || new Error("Could not load export source image.");
}

async function loadExportStampSourceImages(entries, task = null, options = {}) {
  if (!Array.isArray(entries) || !entries.length) {
    return [];
  }

  const urls = Array.from(new Set(
    entries
      .map((entry) => entry?.sourceUrl || "")
      .filter((url) => url && url !== TRANSPARENT_STAMP_SRC)
  ));
  const loadedImages = new Map();
  const failures = [];
  await mapWithConcurrency(urls, 4, async (url, index) => {
    throwIfTaskCancelled(task);
    try {
      const image = await loadExportSourceImageElementWithRetry(url, task, 2, options);
      if (image) {
        loadedImages.set(url, image);
      }
    } catch (error) {
      if (isCancellationError(error)) {
        throw error;
      }
      failures.push({ url, error });
    }
    if (index > 0 && index % EXPORT_CANCEL_CHECK_INTERVAL === 0) {
      await yieldToMainThread(task);
    }
  });

  for (const entry of entries) {
    if (entry && loadedImages.has(entry.sourceUrl)) {
      entry.imageElement = loadedImages.get(entry.sourceUrl);
    }
  }

  if (failures.length && options.strict !== false) {
    const error = new Error(
      failures.length === 1
        ? "One brush image could not be loaded for rendering."
        : `${failures.length} brush images could not be loaded for rendering.`
    );
    error.code = "EXPORT_SOURCE_LOAD_FAILED";
    error.failedSourceUrls = failures.map((failure) => failure.url);
    throw error;
  }
  return failures;
}

function releaseExportEntrySourceImages(entries) {
  const images = new Set();
  for (const entry of Array.isArray(entries) ? entries : []) {
    if (entry?.imageElement instanceof HTMLImageElement) {
      images.add(entry.imageElement);
      delete entry.imageElement;
    }
  }
  for (const image of images) {
    image.onload = null;
    image.onerror = null;
    image.removeAttribute("src");
  }
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

async function prepareExportBackgroundAnimation(options = {}, task = null) {
  if (options.backgroundImageAnimation) {
    return options.backgroundImageAnimation;
  }
  const image = options.backgroundImageElement;
  const imageUrl = image instanceof HTMLImageElement
    ? image.currentSrc || image.getAttribute("src") || image.src || ""
    : "";
  if (!imageUrl || !isGifUrl(imageUrl)) {
    return null;
  }
  try {
    const animation = await waitForExportSourcePromise(
      loadExportBackgroundAnimation(imageUrl),
      task
    );
    throwIfTaskCancelled(task);
    options.backgroundImageAnimation = animation;
    return animation;
  } catch (error) {
    if (isCancellationError(error)) {
      throw error;
    }
    console.warn("Animated export background fell back to its browser frame.", error);
    return null;
  }
}

async function getExportBackgroundImageOptions(task = null) {
  const backgroundSnapshot = {
    imageUrl: typeof state.exportBgImageUrl === "string" ? state.exportBgImageUrl : "",
    enabled: state.exportBackgroundEnabled !== false,
    opacity: clamp(Number(state.exportBgImageOpacity) || 0, 0, 100) / 100,
    mode: state.exportBgImageMode === "tile" ? "tile" : "stretch",
    tileSize: normalizeExportBgTileSize(state.exportBgImageTileSize)
  };
  if (!backgroundSnapshot.imageUrl || !backgroundSnapshot.enabled) {
    return {};
  }

  try {
    const image = await loadExportBackgroundImageElement(backgroundSnapshot.imageUrl, task);
    if (!image) {
      throw new Error("Could not load export background image.");
    }
    return {
      backgroundImageElement: image,
      backgroundImageOpacity: backgroundSnapshot.opacity,
      backgroundImageMode: backgroundSnapshot.mode,
      backgroundImageTileSize: backgroundSnapshot.tileSize
    };
  } catch (error) {
    if (isCancellationError(error)) {
      throw error;
    }
    error.code ||= "EXPORT_BACKGROUND_LOAD_FAILED";
    throw error;
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

function drawExportFrameBackground(ctx, selectionBounds, outputWidth, outputHeight, options = {}) {
  const includeBackground = options.includeBackground !== false;
  const backgroundColor = normalizeHexColor(options.backgroundColor, "#ffffff");
  const matteColor = typeof options.matteColor === "string" ? options.matteColor : "";

  if (includeBackground || matteColor) {
    ctx.save();
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";
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
}

function prepareExportFrame(
  ctx,
  selectionBounds,
  outputWidth,
  outputHeight,
  options = {}
) {
  const selectionWidth = Math.max(1, selectionBounds.right - selectionBounds.left);
  const selectionHeight = Math.max(1, selectionBounds.bottom - selectionBounds.top);
  const scaleX = outputWidth / selectionWidth;
  const scaleY = outputHeight / selectionHeight;

  ctx.clearRect(0, 0, outputWidth, outputHeight);
  if (!options.skipBackground) {
    drawExportFrameBackground(ctx, selectionBounds, outputWidth, outputHeight, options);
  }

  return { scaleX, scaleY };
}

function applyCanvasPixelation(scratchCtx, scratchWidth, scratchHeight, pixelSize) {
  const blockSize = clamp(Math.round(Number(pixelSize) || 0), 1, 64);
  if (blockSize <= 1 || scratchWidth <= 1 || scratchHeight <= 1) {
    return;
  }
  if (!exportPixelateScratchCanvas) {
    exportPixelateScratchCanvas = document.createElement("canvas");
  }
  const reducedWidth = Math.max(1, Math.ceil(scratchWidth / blockSize));
  const reducedHeight = Math.max(1, Math.ceil(scratchHeight / blockSize));
  if (exportPixelateScratchCanvas.width !== reducedWidth) {
    exportPixelateScratchCanvas.width = reducedWidth;
  }
  if (exportPixelateScratchCanvas.height !== reducedHeight) {
    exportPixelateScratchCanvas.height = reducedHeight;
  }
  const pixelCtx = exportPixelateScratchCanvas.getContext("2d", { alpha: true });
  if (!pixelCtx) {
    return;
  }

  try {
    const sourceData = scratchCtx.getImageData(0, 0, scratchWidth, scratchHeight).data;
    const reducedImage = pixelCtx.createImageData(reducedWidth, reducedHeight);
    const targetData = reducedImage.data;
    for (let y = 0; y < reducedHeight; y += 1) {
      const sampleY = Math.min(scratchHeight - 1, Math.floor(y * blockSize + blockSize / 2));
      for (let x = 0; x < reducedWidth; x += 1) {
        const sampleX = Math.min(scratchWidth - 1, Math.floor(x * blockSize + blockSize / 2));
        const sourceOffset = (sampleY * scratchWidth + sampleX) * 4;
        const targetOffset = (y * reducedWidth + x) * 4;
        targetData[targetOffset] = sourceData[sourceOffset];
        targetData[targetOffset + 1] = sourceData[sourceOffset + 1];
        targetData[targetOffset + 2] = sourceData[sourceOffset + 2];
        targetData[targetOffset + 3] = sourceData[sourceOffset + 3];
      }
    }
    pixelCtx.putImageData(reducedImage, 0, 0);
  } catch (error) {
    pixelCtx.clearRect(0, 0, reducedWidth, reducedHeight);
    pixelCtx.imageSmoothingEnabled = false;
    pixelCtx.drawImage(
      exportTintScratchCanvas,
      0,
      0,
      scratchWidth,
      scratchHeight,
      0,
      0,
      reducedWidth,
      reducedHeight
    );
  }

  scratchCtx.clearRect(0, 0, scratchWidth, scratchHeight);
  scratchCtx.globalAlpha = 1;
  scratchCtx.globalCompositeOperation = "source-over";
  scratchCtx.imageSmoothingEnabled = false;
  scratchCtx.drawImage(
    exportPixelateScratchCanvas,
    0,
    0,
    reducedWidth,
    reducedHeight,
    0,
    0,
    scratchWidth,
    scratchHeight
  );
}

function drawExportImageWithTint(
  ctx,
  frameSource,
  drawWidth,
  drawHeight,
  imageRendering,
  tintSettings,
  effects = {}
) {
  const tintLayers = getTintLayerList(tintSettings);
  const pixelateAmount = clamp(Math.round(Number(effects.pixelateAmount) || 0), 0, 64);
  const blurAmount = clamp(Number(effects.blurAmount) || 0, 0, 64);
  if (!tintLayers.length && pixelateAmount <= 0 && blurAmount <= 0) {
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
  scratchCtx.filter = "none";

  if (pixelateAmount > 0) {
    applyCanvasPixelation(scratchCtx, scratchWidth, scratchHeight, pixelateAmount);
  }

  ctx.save();
  if (blurAmount > 0) {
    ctx.filter = `blur(${blurAmount.toFixed(2)}px)`;
  }
  ctx.imageSmoothingEnabled = pixelateAmount > 0 ? false : imageRendering === "auto";
  ctx.drawImage(exportTintScratchCanvas, -drawWidth / 2, -drawHeight / 2, drawWidth, drawHeight);
  ctx.restore();
}

function setCanvasBlendOperation(ctx, blendMode) {
  const operation = getCanvasCompositeOperationForBlendMode(blendMode);
  ctx.globalCompositeOperation = operation;
  if (ctx.globalCompositeOperation !== operation) {
    ctx.globalCompositeOperation = "source-over";
  }
}

function getExportLayerScratchContext(outputWidth, outputHeight) {
  if (!exportLayerScratchCanvas) {
    exportLayerScratchCanvas = document.createElement("canvas");
  }
  if (exportLayerScratchCanvas.width !== outputWidth) {
    exportLayerScratchCanvas.width = outputWidth;
  }
  if (exportLayerScratchCanvas.height !== outputHeight) {
    exportLayerScratchCanvas.height = outputHeight;
  }
  const layerCtx = exportLayerScratchCanvas.getContext("2d", { alpha: true });
  if (!layerCtx) {
    return null;
  }
  layerCtx.clearRect(0, 0, outputWidth, outputHeight);
  layerCtx.globalAlpha = 1;
  layerCtx.globalCompositeOperation = "source-over";
  return layerCtx;
}

function getComparableExportSource(source) {
  const value = String(source || "").trim();
  if (!value || value === TRANSPARENT_STAMP_SRC) {
    return "";
  }
  if (/^(?:data|blob):/i.test(value)) {
    return value;
  }
  try {
    return new URL(value, document.baseURI).href;
  } catch (error) {
    return value;
  }
}

function getRenderableExportEntryElement(entry) {
  const element = entry?.element;
  if (
    !(element instanceof HTMLImageElement) ||
    !element.complete ||
    element.naturalWidth <= 0 ||
    element.naturalHeight <= 0
  ) {
    return null;
  }
  const currentSource = getComparableExportSource(
    element.currentSrc || element.getAttribute("src") || ""
  );
  const expectedSource = getComparableExportSource(entry.sourceUrl);
  if (!currentSource || (expectedSource && currentSource !== expectedSource)) {
    return null;
  }
  return element;
}

function drawExportStampEntry(
  ctx,
  selectionBounds,
  scaleX,
  scaleY,
  entry,
  gifAnimationMap = null,
  timeMs = 0,
  options = {}
) {
  if (entry?.isInSelection === false) {
    return;
  }
  let frameSource = entry.imageElement || getRenderableExportEntryElement(entry);
  if (gifAnimationMap?.has(entry.sourceUrl)) {
    const animation = gifAnimationMap.get(entry.sourceUrl);
    const animatedSource = resolveGifFrameSource(animation, timeMs);
    if (animatedSource) {
      frameSource = animatedSource;
    }
  }
  if (!frameSource) {
    const error = new Error("A brush image was unavailable while rendering.");
    error.code = "EXPORT_SOURCE_UNAVAILABLE";
    error.sourceUrl = entry.sourceUrl || "";
    throw error;
  }

  const drawWidth = entry.width * scaleX;
  const drawHeight = entry.height * scaleY;
  const drawCenterX = (entry.centerX - selectionBounds.left) * scaleX;
  const drawCenterY = (entry.centerY - selectionBounds.top) * scaleY;

  ctx.save();
  ctx.globalAlpha = entry.opacity;
  setCanvasBlendOperation(ctx, options.blendMode || entry.blendMode);
  ctx.imageSmoothingEnabled = entry.imageRendering === "auto";
  ctx.translate(drawCenterX, drawCenterY);
  ctx.rotate((entry.rotation * Math.PI) / 180);
  drawExportImageWithTint(ctx, frameSource, drawWidth, drawHeight, entry.imageRendering, entry.tintSettings, {
    pixelateAmount: entry.pixelateAmount,
    blurAmount: entry.blurAmount
  });
  ctx.restore();
}

function getExportEntryGroupKey(entry) {
  return `${Number.isFinite(Number(entry?.strokeId)) ? Number(entry.strokeId) : "loose"}:${normalizeLayerBlendMode(entry?.blendMode)}`;
}

function drawExportEntryGroup(
  ctx,
  selectionBounds,
  outputWidth,
  outputHeight,
  scaleX,
  scaleY,
  entries,
  startIndex,
  endIndex,
  gifAnimationMap = null,
  timeMs = 0
) {
  const blendMode = normalizeLayerBlendMode(entries[startIndex]?.blendMode);
  if (blendMode === "normal") {
    for (let index = startIndex; index < endIndex; index += 1) {
      drawExportStampEntry(ctx, selectionBounds, scaleX, scaleY, entries[index], gifAnimationMap, timeMs);
    }
    return;
  }

  const layerCtx = getExportLayerScratchContext(outputWidth, outputHeight);
  if (!layerCtx) {
    for (let index = startIndex; index < endIndex; index += 1) {
      drawExportStampEntry(ctx, selectionBounds, scaleX, scaleY, entries[index], gifAnimationMap, timeMs);
    }
    return;
  }

  for (let index = startIndex; index < endIndex; index += 1) {
    drawExportStampEntry(
      layerCtx,
      selectionBounds,
      scaleX,
      scaleY,
      entries[index],
      gifAnimationMap,
      timeMs,
      { blendMode: "normal" }
    );
  }

  ctx.save();
  ctx.globalAlpha = 1;
  setCanvasBlendOperation(ctx, blendMode);
  ctx.drawImage(exportLayerScratchCanvas, 0, 0);
  ctx.restore();
}

function drawExportEntries(
  ctx,
  selectionBounds,
  outputWidth,
  outputHeight,
  scaleX,
  scaleY,
  entries,
  gifAnimationMap = null,
  timeMs = 0
) {
  for (const entry of entries) {
    drawExportStampEntry(ctx, selectionBounds, scaleX, scaleY, entry, gifAnimationMap, timeMs);
  }
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
  const artworkCtx = getExportLayerScratchContext(outputWidth, outputHeight);
  const drawCtx = artworkCtx || ctx;
  const { scaleX, scaleY } = prepareExportFrame(
    drawCtx,
    selectionBounds,
    outputWidth,
    outputHeight,
    { ...options, backgroundImageTimeMs: timeMs, skipBackground: Boolean(artworkCtx) }
  );
  drawExportEntries(
    drawCtx,
    selectionBounds,
    outputWidth,
    outputHeight,
    scaleX,
    scaleY,
    entries,
    gifAnimationMap,
    timeMs
  );
  if (artworkCtx) {
    prepareExportFrame(
      ctx,
      selectionBounds,
      outputWidth,
      outputHeight,
      { ...options, backgroundImageTimeMs: timeMs }
    );
    ctx.save();
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";
    ctx.drawImage(exportLayerScratchCanvas, 0, 0);
    ctx.restore();
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
  const artworkCtx = getExportLayerScratchContext(outputWidth, outputHeight);
  const drawCtx = artworkCtx || ctx;
  const { scaleX, scaleY } = prepareExportFrame(
    drawCtx,
    selectionBounds,
    outputWidth,
    outputHeight,
    { ...options, backgroundImageTimeMs: timeMs, skipBackground: Boolean(artworkCtx) }
  );
  const total = Math.max(1, entries.length);
  for (let index = 0; index < entries.length; index += 1) {
    throwIfTaskCancelled(task);
    drawExportStampEntry(drawCtx, selectionBounds, scaleX, scaleY, entries[index], gifAnimationMap, timeMs);
    if (progress && (index === entries.length - 1 || index % EXPORT_CANCEL_CHECK_INTERVAL === 0)) {
      progress((index + 1) / total);
    }
    if (index > 0 && index % EXPORT_CANCEL_CHECK_INTERVAL === 0) {
      await yieldToMainThread(task);
    }
  }
  if (artworkCtx) {
    prepareExportFrame(
      ctx,
      selectionBounds,
      outputWidth,
      outputHeight,
      { ...options, backgroundImageTimeMs: timeMs }
    );
    ctx.save();
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = "source-over";
    ctx.drawImage(exportLayerScratchCanvas, 0, 0);
    ctx.restore();
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
  return prepareTransparentGifFrameImageData(imageData);
}

function prepareTransparentGifFrameImageData(imageData) {
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

function createExportRasterEntryDto(entry) {
  const sourceUrl = String(entry?.sourceUrl || "");
  if (!sourceUrl || sourceUrl === TRANSPARENT_STAMP_SRC) {
    throw new Error("A worker export stamp has no renderable source.");
  }
  const width = Number(entry.width);
  const height = Number(entry.height);
  const opacity = Number(entry.opacity);
  if (
    !Number.isFinite(width) ||
    width <= 0 ||
    !Number.isFinite(height) ||
    height <= 0 ||
    !Number.isFinite(opacity) ||
    opacity < 0 ||
    opacity > 1
  ) {
    throw new Error("A worker export stamp has invalid geometry or opacity.");
  }
  return {
    sourceId: sourceUrl,
    sourceUrl,
    centerX: Number(entry.centerX) || 0,
    centerY: Number(entry.centerY) || 0,
    width,
    height,
    rotation: Number(entry.rotation) || 0,
    opacity,
    blendMode: normalizeLayerBlendMode(entry.blendMode),
    imageRendering: entry.imageRendering === "auto" ? "auto" : "pixelated",
    tintLayers: getTintLayerList(entry.tintSettings).map((layer) => ({
      color: normalizeHexColor(layer.color, "#ffffff"),
      amountPercent: clamp(Number(layer.amountPercent) || 0, 0, 100)
    })),
    pixelateAmount: clamp(Math.round(Number(entry.pixelateAmount) || 0), 0, 64),
    blurAmount: clamp(Number(entry.blurAmount) || 0, 0, 64)
  };
}

function createExportRasterEntriesDto(entries) {
  return (Array.isArray(entries) ? entries : []).map(createExportRasterEntryDto);
}

function getExportRasterBackgroundImageUrl(options = {}) {
  const image = options.backgroundImageElement;
  if (!(image instanceof HTMLImageElement)) {
    return "";
  }
  return image.currentSrc || image.getAttribute("src") || image.src || "";
}

function createExportRasterBackgroundDto(options = {}) {
  const sourceUrl = getExportRasterBackgroundImageUrl(options);
  const opacity = clamp(Number(options.backgroundImageOpacity) || 0, 0, 1);
  return {
    include: options.includeBackground !== false,
    color: normalizeHexColor(options.backgroundColor, "#ffffff"),
    matteColor: typeof options.matteColor === "string" ? options.matteColor : "",
    image: sourceUrl && opacity > 0
      ? {
          sourceId: sourceUrl,
          sourceUrl,
          opacity,
          mode: options.backgroundImageMode === "tile" ? "tile" : "stretch",
          tileSize: normalizeExportBgTileSize(options.backgroundImageTileSize)
        }
      : null
  };
}

function createExportRasterScene(
  selectionBounds,
  outputWidth,
  outputHeight,
  entries,
  options = {}
) {
  return {
    outputWidth,
    outputHeight,
    ...(
      options.singleGifFrameTimeMs != null &&
      Number.isFinite(Number(options.singleGifFrameTimeMs))
        ? { singleGifFrameTimeMs: Math.max(0, Number(options.singleGifFrameTimeMs)) }
        : {}
    ),
    selectionBounds: {
      left: selectionBounds.left,
      top: selectionBounds.top,
      right: selectionBounds.right,
      bottom: selectionBounds.bottom
    },
    entries: createExportRasterEntriesDto(entries),
    background: createExportRasterBackgroundDto(options)
  };
}

function createExportRasterTimingMap(preparedMessage, entries = [], options = {}) {
  const timingMap = new Map();
  const stampSourceIds = new Set(
    (Array.isArray(entries) ? entries : []).map((entry) => String(entry?.sourceUrl || ""))
  );
  const backgroundSource = getExportRasterBackgroundImageUrl(options);
  if (backgroundSource) {
    stampSourceIds.add(String(backgroundSource));
  }
  for (const asset of Array.isArray(preparedMessage?.assets) ? preparedMessage.assets : []) {
    if (asset?.kind !== "gif" || !stampSourceIds.has(String(asset.id || ""))) {
      continue;
    }
    const durations = normalizeFrameDelays(asset.durations);
    const frameCount = Math.max(1, Number(asset.frameCount) || durations.length || 1);
    timingMap.set(String(asset.id || ""), {
      frames: Array.from({ length: frameCount }, () => null),
      durations: durations.length
        ? durations
        : Array.from({ length: frameCount }, () => EXPORT_GIF_FRAME_DELAY_MS),
      totalDuration: Math.max(
        EXPORT_GIF_FRAME_DELAY_MS,
        Number(asset.totalDurationMs) || durations.reduce((sum, duration) => sum + duration, 0)
      )
    });
  }
  return timingMap;
}

function createExportRasterWorkerSession(task = null, onProgress = null) {
  if (typeof Worker !== "function" || typeof window.OffscreenCanvas !== "function") {
    throw new Error("Worker raster export is unavailable.");
  }

  const worker = new Worker(EXPORT_RASTER_WORKER_URL, { type: "module" });
  const sessionNumber = nextExportRasterSessionId++;
  const jobId = `export-raster-${sessionNumber}`;
  const pending = new Map();
  let requestNumber = 0;
  let closed = false;
  let startupSettled = false;
  let startupResolve = null;
  let startupReject = null;
  const startupPromise = new Promise((resolve, reject) => {
    startupResolve = resolve;
    startupReject = reject;
  });

  const rejectPending = (error) => {
    for (const request of pending.values()) {
      window.clearTimeout(request.timeoutId);
      window.clearTimeout(request.hardTimeoutId);
      request.reject(error);
    }
    pending.clear();
  };

  const closeWithError = (error) => {
    if (closed) {
      return;
    }
    closed = true;
    rejectPending(error);
    if (!startupSettled) {
      startupSettled = true;
      startupReject(error);
    }
    try {
      worker.terminate();
    } catch (workerError) {
      // The worker may already have terminated after a capability failure.
    }
    if (task?.rasterSession === session) {
      task.rasterSession = null;
    }
  };

  const close = (cancelled = false) => {
    closeWithError(
      cancelled
        ? createCancellationError("Export raster work cancelled.")
        : new Error("Export raster worker closed.")
    );
  };

  const session = {
    jobId,
    capabilities: null,
    preparedMessage: null,
    get closed() {
      return closed;
    },
    async start(scene, assets = [], requiredOutput = "") {
      let startupTimeoutId = null;
      let ready;
      try {
        ready = await Promise.race([
          startupPromise,
          new Promise((_, reject) => {
            startupTimeoutId = window.setTimeout(
              () => reject(new Error("Export raster worker startup timed out.")),
              EXPORT_RASTER_STARTUP_TIMEOUT_MS
            );
          })
        ]);
      } finally {
        if (startupTimeoutId !== null) {
          window.clearTimeout(startupTimeoutId);
        }
      }
      throwIfTaskCancelled(task);
      const capabilities = ready?.capabilities || {};
      if (!capabilities.offscreenCanvas2d || !capabilities.gifDisposal) {
        throw new Error("This browser cannot rasterize exports in a worker.");
      }
      if (requiredOutput && capabilities[requiredOutput] !== true) {
        throw new Error(`Worker ${requiredOutput} output is unavailable.`);
      }
      const requiredBlendModes = new Set(
        scene.entries.map((entry) => normalizeLayerBlendMode(entry.blendMode))
      );
      if (
        Array.from(requiredBlendModes).some(
          (blendMode) => !Array.isArray(capabilities.blendModes) || !capabilities.blendModes.includes(blendMode)
        )
      ) {
        throw new Error("This browser cannot reproduce every export blend mode in a worker.");
      }
      if (scene.entries.some((entry) => Number(entry.blurAmount) > 0) && !capabilities.canvasFilter) {
        throw new Error("This browser cannot reproduce blurred exports in a worker.");
      }
      session.capabilities = capabilities;
      session.preparedMessage = await session.request(
        "prepare",
        { jobId, scene, assets },
        EXPORT_RASTER_PREPARE_TIMEOUT_MS
      );
      return session.preparedMessage;
    },
    request(type, payload = {}, timeoutMs = EXPORT_RASTER_FRAME_TIMEOUT_MS) {
      if (closed) {
        return Promise.reject(new Error("Export raster worker is closed."));
      }
      const requestId = `${jobId}-request-${++requestNumber}`;
      return new Promise((resolve, reject) => {
        const request = {
          resolve,
          reject,
          timeoutId: null,
          hardTimeoutId: null,
          timeoutMs,
          type,
          refreshTimeout() {
            window.clearTimeout(request.timeoutId);
            request.timeoutId = window.setTimeout(() => {
              pending.delete(requestId);
              window.clearTimeout(request.hardTimeoutId);
              reject(new Error(`Export raster ${type} stopped making progress.`));
            }, timeoutMs);
          }
        };
        request.refreshTimeout();
        request.hardTimeoutId = window.setTimeout(() => {
          pending.delete(requestId);
          window.clearTimeout(request.timeoutId);
          reject(new Error(`Export raster ${type} exceeded its maximum duration.`));
        }, Math.max(300000, timeoutMs * 5));
        pending.set(requestId, request);
        try {
          worker.postMessage({
            protocol: EXPORT_RASTER_PROTOCOL,
            version: EXPORT_RASTER_VERSION,
            type,
            requestId,
            ...payload
          });
        } catch (error) {
          window.clearTimeout(request.timeoutId);
          window.clearTimeout(request.hardTimeoutId);
          pending.delete(requestId);
          reject(error);
        }
      });
    },
    async renderFrame(output, timeMs = 0, entries = null, background = null) {
      const message = await session.request("render-frame", {
        jobId,
        output,
        timeMs,
        ...(entries ? { entries: createExportRasterEntriesDto(entries) } : {}),
        ...(background ? { background } : {})
      });
      return message.output;
    },
    cancel() {
      if (closed) {
        return;
      }
      try {
        worker.postMessage({
          protocol: EXPORT_RASTER_PROTOCOL,
          version: EXPORT_RASTER_VERSION,
          type: "cancel",
          jobId
        });
      } catch (error) {
        // Terminating below is the authoritative cancellation path.
      }
      close(true);
    },
    release() {
      if (closed) {
        return;
      }
      try {
        worker.postMessage({
          protocol: EXPORT_RASTER_PROTOCOL,
          version: EXPORT_RASTER_VERSION,
          type: "release",
          jobId
        });
      } catch (error) {
        // Terminating below still releases all worker-owned resources.
      }
      close(false);
    }
  };

  worker.addEventListener("message", (event) => {
    const message = event.data || {};
    if (
      message.protocol !== EXPORT_RASTER_PROTOCOL ||
      message.version !== EXPORT_RASTER_VERSION
    ) {
      return;
    }
    if (message.type === "ready" && message.action === "startup") {
      if (!startupSettled) {
        startupSettled = true;
        startupResolve(message);
      }
      return;
    }
    if (message.type === "error" && message.action === "startup") {
      if (!startupSettled) {
        const error = new Error(message.error?.message || "Export raster worker failed to start.");
        error.code = message.error?.code || "EXPORT_RASTER_STARTUP_FAILURE";
        error.capability = message.error?.capability === true;
        startupSettled = true;
        startupReject(error);
      }
      return;
    }
    if (message.type === "progress") {
      const request = pending.get(message.requestId);
      if (request && (!message.jobId || String(message.jobId) === jobId)) {
        request.refreshTimeout();
      }
      onProgress?.(message);
      return;
    }
    const request = pending.get(message.requestId);
    if (!request) {
      return;
    }
    pending.delete(message.requestId);
    window.clearTimeout(request.timeoutId);
    window.clearTimeout(request.hardTimeoutId);
    if (message.type === "error") {
      const error = new Error(message.error?.message || "Export raster worker failed.");
      error.code = message.error?.code || "EXPORT_RASTER_FAILURE";
      error.capability = message.error?.capability === true;
      error.details = message.error?.details || null;
      if (message.error?.cancelled) {
        error.name = "AbortError";
      }
      request.reject(error);
    } else {
      const expectedType = request.type === "prepare"
        ? "prepared"
        : request.type === "render-frame"
        ? "rendered"
        : "";
      if (
        (expectedType && message.type !== expectedType) ||
        (message.jobId != null && String(message.jobId) !== jobId)
      ) {
        request.reject(new Error("Export raster worker returned a mismatched response."));
      } else {
        request.resolve(message);
      }
    }
  });
  worker.addEventListener("error", (event) => {
    const error = new Error(event.message || "Export raster worker crashed.");
    closeWithError(error);
  });
  worker.addEventListener("messageerror", () => {
    const error = new Error("Export raster worker returned an unreadable message.");
    closeWithError(error);
  });

  if (task) {
    task.rasterSession = session;
  }
  return session;
}

async function prepareExportRasterWorkerSession(
  selectionBounds,
  outputWidth,
  outputHeight,
  entries,
  options = {},
  task = null,
  requiredOutput = ""
) {
  const scene = createExportRasterScene(
    selectionBounds,
    outputWidth,
    outputHeight,
    entries,
    options
  );
  const session = createExportRasterWorkerSession(task, (message) => {
    if (message.phase === "assets") {
      const ratio = (Number(message.completed) || 0) / Math.max(1, Number(message.total) || 1);
      updateExportProgress(
        task,
        EXPORT_PROGRESS_COLLECT_END +
          (EXPORT_PROGRESS_DECODE_END - EXPORT_PROGRESS_COLLECT_END) * ratio,
        "Decoding"
      );
    }
  });
  try {
    const prepared = await session.start(scene, [], requiredOutput);
    throwIfTaskCancelled(task);
    return {
      session,
      prepared,
      timingMap: createExportRasterTimingMap(prepared, entries, options)
    };
  } catch (error) {
    session.release();
    throw error;
  }
}

function exportRasterSourceRequiresLiveBrowserFrame(sourceUrl, element = null) {
  const source = String(sourceUrl || "");
  if (!source) {
    return false;
  }
  const metadata = getStockBrushMetadataForSource(source);
  const brushId = Number(element?.dataset?.brushId);
  const brush = Number.isFinite(brushId) ? findBrushById(brushId) : null;
  if (isGifUrl(source) || (brush && getBrushSourceIsGif(brush))) {
    return false;
  }
  if (metadata) {
    // The raster worker only has deterministic animation decoding for GIF.
    // Keep animated non-GIF assets on the browser compatibility renderer so
    // they are never silently substituted with a static first frame.
    return metadata.animated === true;
  }
  if (brush?.animated === true) {
    return true;
  }
  const mimeType = getSceneRendererMimeType(source);
  const originalMimeType = brush ? getSceneRendererMimeType(getBrushPrimarySourceUrl(brush)) : "";
  return Boolean(
    /^(?:image\/(?:png|webp|avif|svg\+xml))$/i.test(mimeType) ||
    /^(?:image\/(?:png|webp|avif|svg\+xml))$/i.test(originalMimeType) ||
    /^(?:blob:)/i.test(source) ||
    /\.(?:png|webp|avif|svg)(?:[?#]|$)/i.test(source)
  );
}

function shouldTryExportRasterWorker(entries = [], options = {}) {
  const backgroundSource = getExportRasterBackgroundImageUrl(options);
  return Boolean(
    !options.sequenceExportActive &&
    typeof Worker === "function" &&
    typeof window.OffscreenCanvas === "function" &&
    !(Array.isArray(entries) ? entries : []).some((entry) =>
      exportRasterSourceRequiresLiveBrowserFrame(entry?.sourceUrl, entry?.element)
    ) &&
    !exportRasterSourceRequiresLiveBrowserFrame(backgroundSource)
  );
}

function isExportRasterSafetyError(error) {
  return [
    "MEMORY_BUDGET_EXCEEDED",
    "MEMORY_ESTIMATE_OVERFLOW",
    "SOURCE_TOO_LARGE",
    "GIF_FRAME_LIMIT_EXCEEDED"
  ].includes(String(error?.code || ""));
}

async function renderExportPngBlob(selectionBounds, outputWidth, outputHeight, entries, options = {}, task = null) {
  const frameTimeMs = Math.max(0, Number(options.frameTimeMs) || 0);
  if (options.preferMainRenderer !== true && shouldTryExportRasterWorker(entries, options)) {
    let raster = null;
    try {
      raster = await prepareExportRasterWorkerSession(
        selectionBounds,
        outputWidth,
        outputHeight,
        entries,
        options,
        task,
        "png"
      );
      if (!raster.session.capabilities?.png) {
        throw new Error("Worker PNG encoding is unavailable.");
      }
      const output = await raster.session.renderFrame("png", frameTimeMs);
      throwIfTaskCancelled(task);
      if (
        output?.kind !== "png" ||
        !(output.blob instanceof Blob) ||
        output.blob.type !== "image/png" ||
        Number(output.width) !== outputWidth ||
        Number(output.height) !== outputHeight
      ) {
        throw new Error("Worker PNG output was invalid.");
      }
      updateExportProgress(task, EXPORT_PROGRESS_DRAW_END, "Drawing");
      updateExportProgress(task, EXPORT_PROGRESS_PNG_ENCODE_HOLD, "Encoding");
      return output.blob;
    } catch (error) {
      if (isCancellationError(error) || task?.cancelled) {
        throw createCancellationError();
      }
      if (isExportRasterSafetyError(error)) {
        throw error;
      }
      console.warn("Worker PNG export fell back to the main renderer.", error);
    } finally {
      raster?.session.release();
    }
  }
  const canvas = document.createElement("canvas");
  canvas.width = outputWidth;
  canvas.height = outputHeight;
  const ctx = canvas.getContext("2d", { alpha: true });
  if (!ctx) {
    throw new Error("Could not create export canvas.");
  }
  const releaseSourceImages = options.releaseSourceImagesAfterRender === true;
  try {
    await loadExportStampSourceImages(entries, task, {
      cache: !releaseSourceImages
    });
    throwIfTaskCancelled(task);
    await drawExportFrameAsync(
      ctx,
      selectionBounds,
      outputWidth,
      outputHeight,
      entries,
      null,
      frameTimeMs,
      { ...options, sequenceTimeMs: options.sequenceExportActive ? (Number(options.sequencePrewarmMs) || 0) : null },
      task,
      (ratio) => updateExportProgress(
        task,
        EXPORT_PROGRESS_COLLECT_END + (EXPORT_PROGRESS_DRAW_END - EXPORT_PROGRESS_COLLECT_END) * ratio,
        "Drawing"
      )
    );
    throwIfTaskCancelled(task);
    updateExportProgress(task, EXPORT_PROGRESS_PNG_ENCODE_HOLD, "Encoding");
    return await canvasToPngBlob(canvas);
  } finally {
    if (releaseSourceImages) {
      releaseExportEntrySourceImages(entries);
    }
  }
}

async function prepareExportGifRenderAssets(entries, options = {}, task = null) {
  await prepareExportBackgroundAnimation(options, task);
  throwIfTaskCancelled(task);
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
  await loadExportStampSourceImages(entries, task);
  throwIfTaskCancelled(task);
  return gifAnimationMap;
}

function formatExportByteSize(bytes) {
  const value = Math.max(0, Number(bytes) || 0);
  return `${(value / 1000000).toFixed(value >= 10000000 ? 1 : 2)}mb`;
}

function releaseGifEncoderFrames(gif) {
  if (!gif || typeof gif !== "object") {
    return;
  }
  if (Array.isArray(gif.frames)) {
    for (const frame of gif.frames) {
      if (!frame || typeof frame !== "object") {
        continue;
      }
      frame.data = null;
      frame.context = null;
      frame.image = null;
    }
    gif.frames.length = 0;
  }
  gif.groups?.clear?.();
  if (Array.isArray(gif.imageParts)) {
    gif.imageParts.length = 0;
  }
  const encoderWorkers = new Set([
    ...(Array.isArray(gif.freeWorkers) ? gif.freeWorkers : []),
    ...(Array.isArray(gif.activeWorkers) ? gif.activeWorkers : [])
  ]);
  for (const worker of encoderWorkers) {
    try {
      worker.onmessage = null;
      worker.onerror = null;
      worker.terminate?.();
    } catch {
      // The worker may already have been terminated by gif.js.
    }
  }
  if (Array.isArray(gif.freeWorkers)) {
    gif.freeWorkers.length = 0;
  }
  if (Array.isArray(gif.activeWorkers)) {
    gif.activeWorkers.length = 0;
  }
  gif.running = false;
}

function getGifEncoderFrameBudgetBytes() {
  const deviceMemory = Number(navigator.deviceMemory);
  if (Number.isFinite(deviceMemory) && deviceMemory <= 4) {
    return 80 * 1024 * 1024;
  }
  if (Number.isFinite(deviceMemory) && deviceMemory <= 8) {
    return 128 * 1024 * 1024;
  }
  if (Number.isFinite(deviceMemory) && deviceMemory > 8) {
    return 192 * 1024 * 1024;
  }
  return EXPORT_GIF_ENCODER_DEFAULT_FRAME_BUDGET_BYTES;
}

function getMemoryBoundedGifFrameDelays(width, height, frameDelays) {
  const normalizedDelays = normalizeFrameDelays(frameDelays);
  const safeDelays = normalizedDelays.length ? normalizedDelays : [EXPORT_GIF_FRAME_DELAY_MS];
  const bytesPerFrame = Math.max(1, Math.round(Number(width) || 1)) *
    Math.max(1, Math.round(Number(height) || 1)) * 4;
  const maxFrameCount = Math.floor(getGifEncoderFrameBudgetBytes() / bytesPerFrame);
  if (maxFrameCount < 1) {
    const error = new Error("The requested GIF dimensions exceed the safe encoder memory budget.");
    error.code = "MEMORY_BUDGET_EXCEEDED";
    throw error;
  }
  if (safeDelays.length <= maxFrameCount) {
    return safeDelays;
  }
  const boundedDelays = createExportFrameDelaysForCount(
    getFrameDelaysDuration(safeDelays),
    maxFrameCount
  );
  updateBrushStatus(
    `GIF sampled to ${boundedDelays.length} frames at this resolution to fit memory safely.`
  );
  return boundedDelays;
}

function estimateGifExportBytes(width, height, frameCount, entries) {
  const pixels = Math.max(1, Number(width) || 1) *
    Math.max(1, Number(height) || 1) *
    Math.max(1, Number(frameCount) || 1);
  const stampFactor = clamp((Array.isArray(entries) ? entries.length : 0) / 1200, 0, 0.08);
  return 65000 + Math.max(1, Number(frameCount) || 1) * 4200 + pixels * (0.045 + stampFactor);
}

function getGifSizeLimitPriority(options = {}) {
  return options.animationAuto !== false ? "frames" : "resolution";
}

function normalizeGifSizeLimitPlan(plan) {
  return {
    width: Math.max(1, Math.round(Number(plan?.width) || 1)),
    height: Math.max(1, Math.round(Number(plan?.height) || 1)),
    frameCount: clamp(
      Math.round(Number(plan?.frameCount) || 1),
      1,
      EXPORT_MAX_FRAME_COUNT
    )
  };
}

function gifSizeLimitPlansMatch(left, right) {
  return Boolean(
    left &&
      right &&
      left.width === right.width &&
      left.height === right.height &&
      left.frameCount === right.frameCount
  );
}

function reduceGifSizeLimitPlan(plan, ratio, priority) {
  const safePlan = normalizeGifSizeLimitPlan(plan);
  const safeRatio = clamp(Number(ratio) || 0.5, 0.04, 0.96);
  const minFrames = Math.min(safePlan.frameCount, EXPORT_GIF_SIZE_LIMIT_MIN_FRAMES);
  const reduceFrames = () => {
    if (safePlan.frameCount <= minFrames) {
      return null;
    }
    let frameCount = Math.max(minFrames, Math.floor(safePlan.frameCount * safeRatio));
    if (frameCount >= safePlan.frameCount) {
      frameCount = safePlan.frameCount - 1;
    }
    return { ...safePlan, frameCount };
  };
  const reduceResolution = () => {
    if (safePlan.width <= 1 && safePlan.height <= 1) {
      return null;
    }
    const scale = Math.sqrt(safeRatio);
    const width = Math.max(1, Math.floor(safePlan.width * scale));
    const height = Math.max(1, Math.floor(safePlan.height * scale));
    if (width === safePlan.width && height === safePlan.height) {
      return null;
    }
    return { ...safePlan, width, height };
  };

  return normalizeGifSizeLimitPlan(
    priority === "frames"
      ? reduceFrames() || reduceResolution() || { ...safePlan, frameCount: 1 }
      : reduceResolution() || reduceFrames() || { width: 1, height: 1, frameCount: safePlan.frameCount }
  );
}

function createInitialGifSizeLimitPlan(width, height, frameDelays, entries, options = {}) {
  const plan = normalizeGifSizeLimitPlan({
    width,
    height,
    frameCount: Math.max(1, normalizeFrameDelays(frameDelays).length)
  });
  const estimate = estimateGifExportBytes(plan.width, plan.height, plan.frameCount, entries);
  if (estimate <= EXPORT_GIF_MAX_SIZE_BYTES * 1.35) {
    return plan;
  }
  return reduceGifSizeLimitPlan(
    plan,
    EXPORT_GIF_SIZE_TARGET_BYTES / estimate,
    getGifSizeLimitPriority(options)
  );
}

function getEstimatedGifFrameDelaysForSizeLimit(options = {}) {
  const frameCountOverride = Number(options.frameCountOverride);
  if (Number.isFinite(frameCountOverride) && frameCountOverride > 0) {
    return createExportFrameDelays(0, frameCountOverride);
  }
  if (options.animationAuto === false) {
    const manualSeconds = EXPORT_MANUAL_SECONDS_PRESETS.includes(Number(options.animationSeconds))
      ? Number(options.animationSeconds)
      : 1;
    return createExportFrameDelays(manualSeconds * 1000);
  }
  return createExportFrameDelays(EXPORT_GIF_DURATION_MS);
}

async function renderExportGifBlobWithSizeLimit(
  selectionBounds,
  outputWidth,
  outputHeight,
  entries,
  options = {},
  task = null
) {
  if (shouldTryExportRasterWorker(entries, options) && !(options.gifAnimationMap instanceof Map)) {
    try {
      const estimatedFrameDelays = getEstimatedGifFrameDelaysForSizeLimit(options);
      let plan = createInitialGifSizeLimitPlan(
        outputWidth,
        outputHeight,
        estimatedFrameDelays,
        entries,
        options
      );
      const priority = getGifSizeLimitPriority(options);
      let baseFrameDelays = null;
      let durationMs = 0;
      for (let attempt = 0; attempt < EXPORT_GIF_SIZE_LIMIT_MAX_ATTEMPTS; attempt += 1) {
        throwIfTaskCancelled(task);
        const frameDelays = baseFrameDelays
          ? plan.frameCount === baseFrameDelays.length
            ? baseFrameDelays
            : createExportFrameDelaysForCount(durationMs, plan.frameCount)
          : plan.frameCount < estimatedFrameDelays.length
            ? createExportFrameDelaysForCount(
                getFrameDelaysDuration(estimatedFrameDelays),
                plan.frameCount
              )
            : null;
        const result = await renderExportGifBlobWithRasterWorker(
          selectionBounds,
          plan.width,
          plan.height,
          entries,
          {
            ...options,
            ...(frameDelays ? { frameDelaysOverride: frameDelays } : {}),
            returnRenderDetails: true
          },
          task
        );
        const blob = result?.blob;
        if (!(blob instanceof Blob)) {
          throw new Error("Worker GIF sizing returned an invalid result.");
        }
        if (!baseFrameDelays) {
          baseFrameDelays = normalizeFrameDelays(result.frameDelays);
          if (!baseFrameDelays.length) {
            baseFrameDelays = [EXPORT_GIF_FRAME_DELAY_MS];
          }
          durationMs = getFrameDelaysDuration(baseFrameDelays);
          plan.frameCount = baseFrameDelays.length;
        }
        throwIfTaskCancelled(task);
        if (blob.size <= EXPORT_GIF_MAX_SIZE_BYTES) {
          if (
            attempt > 0 ||
            plan.width !== outputWidth ||
            plan.height !== outputHeight ||
            plan.frameCount !== baseFrameDelays.length
          ) {
            updateBrushStatus(
              `GIF sized to ${formatExportByteSize(blob.size)} (${plan.width}x${plan.height}, ${plan.frameCount} frames).`
            );
          }
          return blob;
        }
        updateBrushStatus(
          `GIF was ${formatExportByteSize(blob.size)}; reducing toward 15mb...`
        );
        updateExportProgress(task, EXPORT_PROGRESS_DRAW_END, "Sizing");
        const nextPlan = reduceGifSizeLimitPlan(
          plan,
          EXPORT_GIF_SIZE_TARGET_BYTES / Math.max(1, blob.size),
          priority
        );
        plan = gifSizeLimitPlansMatch(nextPlan, plan)
          ? reduceGifSizeLimitPlan(plan, 0.65, priority === "frames" ? "resolution" : "frames")
          : nextPlan;
        await yieldToMainThread(task);
      }
      const error = new Error("Could not reduce GIF below 15mb.");
      error.code = "EXPORT_GIF_SIZE_LIMIT_FAILED";
      throw error;
    } catch (error) {
      if (isCancellationError(error) || task?.cancelled) {
        throw createCancellationError();
      }
      if (isExportRasterSafetyError(error)) {
        throw error;
      }
      if (error?.code === "EXPORT_GIF_SIZE_LIMIT_FAILED") {
        throw error;
      }
      console.warn("Worker GIF sizing fell back to the main renderer.", error);
    }
  }
  const gifAnimationMap = await prepareExportGifRenderAssets(entries, options, task);
  const baseFrameDelays = getExportGifFrameDelays(gifAnimationMap, options);
  const durationMs = getExportGifDurationMs(gifAnimationMap, options);
  let plan = createInitialGifSizeLimitPlan(
    outputWidth,
    outputHeight,
    baseFrameDelays,
    entries,
    options
  );
  const priority = getGifSizeLimitPriority(options);
  let lastBlob = null;

  for (let attempt = 0; attempt < EXPORT_GIF_SIZE_LIMIT_MAX_ATTEMPTS; attempt += 1) {
    throwIfTaskCancelled(task);
    const frameDelays = plan.frameCount === baseFrameDelays.length
      ? baseFrameDelays
      : createExportFrameDelaysForCount(durationMs, plan.frameCount);
    const blob = await renderExportGifBlob(
      selectionBounds,
      plan.width,
      plan.height,
      entries,
      {
        ...options,
        gifAnimationMap,
        sourceImagesLoaded: true,
        frameDelaysOverride: frameDelays
      },
      task
    );
    lastBlob = blob;
    throwIfTaskCancelled(task);
    if (blob.size <= EXPORT_GIF_MAX_SIZE_BYTES) {
      if (attempt > 0 || plan.width !== outputWidth || plan.height !== outputHeight || plan.frameCount !== baseFrameDelays.length) {
        updateBrushStatus(
          `GIF sized to ${formatExportByteSize(blob.size)} (${plan.width}x${plan.height}, ${frameDelays.length} frames).`
        );
      }
      return blob;
    }

    updateBrushStatus(
      `GIF was ${formatExportByteSize(blob.size)}; reducing toward 15mb...`
    );
    updateExportProgress(task, EXPORT_PROGRESS_DRAW_END, "Sizing");
    const nextPlan = reduceGifSizeLimitPlan(
      plan,
      EXPORT_GIF_SIZE_TARGET_BYTES / Math.max(1, blob.size),
      priority
    );
    if (gifSizeLimitPlansMatch(nextPlan, plan)) {
      plan = reduceGifSizeLimitPlan(plan, 0.65, priority === "frames" ? "resolution" : "frames");
    } else {
      plan = nextPlan;
    }
    await yieldToMainThread(task);
  }

  if (lastBlob && lastBlob.size <= EXPORT_GIF_MAX_SIZE_BYTES) {
    return lastBlob;
  }
  throw new Error("Could not reduce GIF below 15mb.");
}

async function renderExportGifBlobWithRasterWorker(
  selectionBounds,
  outputWidth,
  outputHeight,
  entries,
  options = {},
  task = null
) {
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
  let raster = null;
  let gif = null;
  try {
    raster = await prepareExportRasterWorkerSession(
      selectionBounds,
      outputWidth,
      outputHeight,
      entries,
      frameOptions,
      task,
      "rgba"
    );
    if (!raster.session.capabilities?.rgba) {
      throw new Error("Worker RGBA export is unavailable.");
    }
    const overrideFrameDelays = normalizeFrameDelays(options.frameDelaysOverride);
    const requestedFrameDelays = overrideFrameDelays.length
      ? overrideFrameDelays
      : getExportGifFrameDelays(raster.timingMap, options);
    const frameDelays = getMemoryBoundedGifFrameDelays(
      outputWidth,
      outputHeight,
      requestedFrameDelays
    );

    gif = new window.GIF({
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
      const output = await raster.session.renderFrame("rgba", elapsedMs);
      if (
        output?.kind !== "rgba" ||
        !(output.buffer instanceof ArrayBuffer) ||
        output.buffer.byteLength !== outputWidth * outputHeight * 4 ||
        Number(output.width) !== outputWidth ||
        Number(output.height) !== outputHeight
      ) {
        throw new Error("Worker GIF frame output was invalid.");
      }
      let imageData = new ImageData(
        new Uint8ClampedArray(output.buffer),
        outputWidth,
        outputHeight
      );
      if (!includeBackground) {
        imageData = prepareTransparentGifFrameImageData(imageData);
      }
      gif.addFrame(imageData, {
        delay: frameDelays[index],
        dispose: 2
      });
      elapsedMs += frameDelays[index];
      updateExportProgress(
        task,
        EXPORT_PROGRESS_DECODE_END +
          (EXPORT_PROGRESS_DRAW_END - EXPORT_PROGRESS_DECODE_END) *
            ((index + 1) / Math.max(1, frameDelays.length)),
        "Drawing"
      );
    }

    raster.session.release();
    raster = null;
    const blob = await new Promise((resolve, reject) => {
      const clearGifTask = () => {
        if (task?.gif === gif) {
          task.gif = null;
        }
      };
      gif.on("progress", (ratio) => {
        updateExportProgress(
          task,
          EXPORT_PROGRESS_DRAW_END +
            (EXPORT_PROGRESS_ENCODE_END - EXPORT_PROGRESS_DRAW_END) * ratio,
          "Encoding"
        );
      });
      gif.on("finished", (blob) => {
        clearGifTask();
        releaseGifEncoderFrames(gif);
        if (task?.cancelled) {
          reject(createCancellationError());
          return;
        }
        resolve(blob);
      });
      gif.on("abort", () => {
        clearGifTask();
        releaseGifEncoderFrames(gif);
        reject(createCancellationError());
      });
      throwIfTaskCancelled(task);
      gif.render();
    });
    return options.returnRenderDetails === true
      ? { blob, frameDelays }
      : blob;
  } catch (error) {
    if (task?.gif === gif) {
      task.gif = null;
    }
    releaseGifEncoderFrames(gif);
    throw error;
  } finally {
    raster?.session.release();
  }
}

async function renderExportGifBlob(selectionBounds, outputWidth, outputHeight, entries, options = {}, task = null) {
  if (shouldTryExportRasterWorker(entries, options) && !(options.gifAnimationMap instanceof Map)) {
    try {
      return await renderExportGifBlobWithRasterWorker(
        selectionBounds,
        outputWidth,
        outputHeight,
        entries,
        options,
        task
      );
    } catch (error) {
      if (isCancellationError(error) || task?.cancelled) {
        throw createCancellationError();
      }
      if (isExportRasterSafetyError(error)) {
        throw error;
      }
      console.warn("Worker GIF rasterization fell back to the main renderer.", error);
    }
  }
  await prepareExportBackgroundAnimation(options, task);
  throwIfTaskCancelled(task);
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
  let sourceImagesLoaded = options.sourceImagesLoaded === true;
  const gifAnimationMap = options.gifAnimationMap instanceof Map
    ? options.gifAnimationMap
    : await prepareExportGifRenderAssets(entries, options, task);
  if (!(options.gifAnimationMap instanceof Map)) {
    sourceImagesLoaded = true;
  }
  if (!sourceImagesLoaded) {
    await loadExportStampSourceImages(entries, task);
    throwIfTaskCancelled(task);
  }
  const overrideFrameDelays = normalizeFrameDelays(options.frameDelaysOverride);
  const requestedFrameDelays = overrideFrameDelays.length
    ? overrideFrameDelays
    : getExportGifFrameDelays(gifAnimationMap, options);
  const frameDelays = getMemoryBoundedGifFrameDelays(
    outputWidth,
    outputHeight,
    requestedFrameDelays
  );

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
  const sequencePrewarmMs = Number(options.sequencePrewarmMs) || 0;
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
      { ...frameOptions, sequenceTimeMs: options.sequenceExportActive ? sequencePrewarmMs + elapsedMs : null },
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
      releaseGifEncoderFrames(gif);
      if (task && task.cancelled) {
        reject(createCancellationError());
        return;
      }
      resolve(blob);
    });
    gif.on("abort", () => {
      clearGifTask();
      releaseGifEncoderFrames(gif);
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
  const videoTrack = stream.getVideoTracks()[0] || null;
  const requestVideoFrame = () => {
    if (videoTrack && typeof videoTrack.requestFrame === "function") {
      try {
        videoTrack.requestFrame();
      } catch (error) {
        // Some browsers expose requestFrame but reject it while recording starts/stops.
      }
    }
  };
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

  await prepareExportBackgroundAnimation(options, task);
  throwIfTaskCancelled(task);
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
  await loadExportStampSourceImages(entries, task);
  throwIfTaskCancelled(task);

  const durationMs = getExportVideoDurationMs(gifAnimationMap, options);
  const frameIntervalMs = 1000 / EXPORT_VIDEO_FPS;
  const frameOptions = {
    ...options,
    includeBackground: options.includeBackground !== false
  };
  const sequencePrewarmMs = Number(options.sequencePrewarmMs) || 0;

  await drawExportFrameAsync(
    renderCtx,
    selectionBounds,
    outputWidth,
    outputHeight,
    entries,
    gifAnimationMap,
    0,
    { ...frameOptions, sequenceTimeMs: options.sequenceExportActive ? sequencePrewarmMs : null },
    task
  );
  recordCtx.clearRect(0, 0, outputWidth, outputHeight);
  recordCtx.drawImage(renderCanvas, 0, 0);
  requestVideoFrame();

  recorder.start(250);
  const recordingStartTime = performance.now();
  let recorderStopTimerId = null;
  const stopRecorderIfActive = () => {
    if (recorder.state === "recording") {
      try {
        if (typeof recorder.requestData === "function") {
          recorder.requestData();
        }
        recorder.stop();
      } catch (error) {
        // Recorder may already be stopping after cancellation or timeout.
      }
    }
  };
  recorderStopTimerId = window.setTimeout(stopRecorderIfActive, durationMs);
  await yieldToMainThread(task);
  try {
    const recordingEndTime = recordingStartTime + durationMs;
    let nextFrameTargetTime = recordingStartTime;
    let estimatedRenderMs = frameIntervalMs;

    while (true) {
      throwIfTaskCancelled(task);
      if (recorder.state !== "recording") {
        break;
      }
      const now = performance.now();
      const elapsedMs = Math.max(0, now - recordingStartTime);
      const remainingMs = recordingEndTime - now;
      if (elapsedMs >= durationMs || remainingMs <= 0) {
        break;
      }

      if (remainingMs < Math.max(frameIntervalMs, estimatedRenderMs * 1.25 + 4)) {
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
        { ...frameOptions, sequenceTimeMs: options.sequenceExportActive ? sequencePrewarmMs + frameTimeMs : null }
      );
      recordCtx.clearRect(0, 0, outputWidth, outputHeight);
      recordCtx.drawImage(renderCanvas, 0, 0);
      requestVideoFrame();

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
    requestVideoFrame();
    stopRecorderIfActive();
    return await recordedBlobPromise;
  } finally {
    if (recorderStopTimerId !== null) {
      window.clearTimeout(recorderStopTimerId);
    }
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
  updateBrushCursorPreview();
  const timestamp = Date.now();
  const exportOptions = {
    includeBackground: Boolean(state.exportBackgroundEnabled),
    backgroundColor: state.canvasBackgroundColor,
    animationAuto: state.exportAnimationAuto !== false,
    animationSeconds: state.exportAnimationSeconds,
    frameCountOverride: state.exportAnimationAuto === false ? getExportFrameCountOverride() : null,
    sequencePrewarmMs: getExportSequencePrewarmMs(),
    gifSizeLimitEnabled: Boolean(state.exportGifSizeLimitEnabled),
    sequenceExportActive: hasActiveSequenceEffectOnCanvas()
  };
  const sequenceSnapshot = exportOptions.sequenceExportActive ? createSequenceExportSnapshot() : null;

  exportButton.disabled = true;
  exportCancelButton.disabled = false;
  exportButton.classList.add("is-loading");
  updateExportProgress(task, 0, "Exporting");
  updateBrushStatus("Exporting... Press Esc to cancel.");
  try {
    Object.assign(exportOptions, await getExportBackgroundImageOptions(task));
    throwIfTaskCancelled(task);
    if (sequenceSnapshot) {
      state.sequenceExportActive = true;
      resetSequencesForExport();
      updateExportProgress(task, EXPORT_PROGRESS_COLLECT_END * 0.25, "Pre-warming");
      await prewarmSequencesForExport(exportOptions.sequencePrewarmMs, task);
    }
    const entries = await collectExportStampEntries(
      normalized,
      task,
      (ratio) => updateExportProgress(task, EXPORT_PROGRESS_COLLECT_END * ratio, "Collecting"),
      { includeSequenceCandidates: exportOptions.sequenceExportActive }
    );
    throwIfTaskCancelled(task);
    const hasGif =
      hasGifStampOnCanvas() ||
      exportOptions.sequenceExportActive ||
      isGifUrl(getExportRasterBackgroundImageUrl(exportOptions));
    const blob = hasGif
      ? exportOptions.gifSizeLimitEnabled
        ? await renderExportGifBlobWithSizeLimit(normalized, resolution.width, resolution.height, entries, exportOptions, task)
        : await renderExportGifBlob(normalized, resolution.width, resolution.height, entries, exportOptions, task)
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
    } else if (error?.code === "MEMORY_BUDGET_EXCEEDED") {
      console.error("GIF export exceeded the safe raster memory budget.", error);
      updateBrushStatus("Could not complete export safely. Try a lower export scale.");
    } else if (isExportRasterSafetyError(error)) {
      console.error("GIF export exceeded a safe raster limit.", error);
      updateBrushStatus("Could not complete export safely with this source or scale.");
    } else if (
      error?.code === "EXPORT_BACKGROUND_LOAD_FAILED" ||
      error?.code === "EXPORT_SOURCE_LOAD_TIMEOUT"
    ) {
      console.error("GIF export could not load the selected background.", error);
      updateBrushStatus("Could not complete export because the background image could not be read.");
    } else if (
      error?.code === "EXPORT_SOURCE_LOAD_FAILED" ||
      error?.code === "EXPORT_SOURCE_UNAVAILABLE" ||
      error?.code === "EXPORT_GIF_DECODE_FAILED"
    ) {
      console.error("GIF export could not load a brush source.", error);
      updateBrushStatus("Could not complete export because a brush image could not be read.");
    } else {
      console.error("GIF export failed.", error);
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
    refreshLayerSequenceLoop();
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
  updateBrushCursorPreview();
  const timestamp = Date.now();
  state.exportVideoAuto = exportVideoAutoToggle ? exportVideoAutoToggle.checked : state.exportVideoAuto !== false;
  const manualVideoDurationMs = state.exportVideoAuto === false ? getManualExportVideoDurationMs() : null;
  const exportOptions = {
    includeBackground: Boolean(state.exportBackgroundEnabled),
    backgroundColor: state.canvasBackgroundColor,
    videoAuto: state.exportVideoAuto !== false,
    videoSeconds: state.exportVideoSeconds,
    videoDurationMs: manualVideoDurationMs,
    sequencePrewarmMs: getExportSequencePrewarmMs(),
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
    Object.assign(exportOptions, await getExportBackgroundImageOptions(task));
    throwIfTaskCancelled(task);
    if (sequenceSnapshot) {
      state.sequenceExportActive = true;
      resetSequencesForExport();
      updateExportProgress(task, EXPORT_PROGRESS_COLLECT_END * 0.25, "Pre-warming");
      await prewarmSequencesForExport(exportOptions.sequencePrewarmMs, task);
    }
    const entries = await collectExportStampEntries(
      normalized,
      task,
      (ratio) => updateExportProgress(task, EXPORT_PROGRESS_COLLECT_END * ratio, "Collecting"),
      { includeSequenceCandidates: exportOptions.sequenceExportActive }
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
    } else if (
      error?.code === "EXPORT_BACKGROUND_LOAD_FAILED" ||
      error?.code === "EXPORT_SOURCE_LOAD_TIMEOUT"
    ) {
      console.error("Video export could not load the selected background.", error);
      updateBrushStatus("Could not complete video export because the background image could not be read.");
    } else {
      console.error("Video export failed.", error);
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
    refreshLayerSequenceLoop();
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

function createBrushFromSourceData(brushData) {
  const brush = {
    id: state.nextBrushId,
    ...brushData
  };
  state.nextBrushId += 1;
  return brush;
}

function getStockBrushFolderSourceUrls(folder) {
  return getStockBrushFiles(folder).map((filePath) =>
    getCanonicalStockBrushSource(encodeStockBrushPath(filePath))
  );
}

function getBrushPrimarySourceUrl(brush) {
  return getCanonicalStockBrushSource(brush?.originalUrl || brush?.url || "");
}

function refreshBrushDataAfterLoad(releaseUrls = []) {
  resetBrushGalleryForBrushSetChange();
  clearBrushFrameCountJobs();
  state.soloBrushId = null;
  clearSelectedBrushes();
  state.brushCursorPreview.brushId = null;
  resetBrushCursorPreviewSource();
  for (const oldUrl of releaseUrls) {
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

async function loadStockBrushFolder(folderId, options = {}) {
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
    if (options.additive) {
      const activeFolderIds = getActiveStockBrushFolderIdSet();
      const folderSourceUrls = new Set(getStockBrushFolderSourceUrls(folder));
      if (activeFolderIds.has(folder.id)) {
        const removedUrls = [];
        state.brushes = state.brushes.filter((brush) => {
          if (folderSourceUrls.has(getBrushPrimarySourceUrl(brush))) {
            removedUrls.push(brush.url);
            return false;
          }
          return true;
        });
        activeFolderIds.delete(folder.id);
        setActiveStockBrushFolders(
          Array.from(activeFolderIds),
          activeFolderIds.size > 1 ? "multi" : "single"
        );
        refreshBrushDataAfterLoad(removedUrls);
        return;
      }

      const existingSources = new Set(state.brushes.map(getBrushPrimarySourceUrl));
      const filesToLoad = files.filter((filePath) =>
        !existingSources.has(getCanonicalStockBrushSource(encodeStockBrushPath(filePath)))
      );
      if (filesToLoad.length) {
        const loaded = await loadStockBrushFileData(filesToLoad);
        if (!loaded.length) {
          updateBrushStatus(`Could not load ${folder.name} stock brushes.`);
          return;
        }
        state.brushes.push(...loaded.map(createBrushFromSourceData));
      }
      activeFolderIds.add(folder.id);
      setActiveStockBrushFolders(
        Array.from(activeFolderIds),
        activeFolderIds.size > 1 ? "multi" : "single"
      );
      refreshBrushDataAfterLoad();
      return;
    }

    const loaded = await loadStockBrushFileData(files);
    if (!loaded.length) {
      updateBrushStatus(`Could not load ${folder.name} stock brushes.`);
      return;
    }
    const previousBrushUrls = state.brushes.map((brush) => brush.url);
    state.brushes = loaded.map(createBrushFromSourceData);
    setActiveStockBrushFolders([folder.id], "single");
    clearActiveCustomBrushPreset();
    refreshBrushDataAfterLoad(previousBrushUrls);
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
    tags: getBrushTags(brushData),
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
    new Set(sources.map(getCanonicalStockBrushSource).filter(Boolean))
  );
  const loadedBrushData = await mapWithConcurrency(
    uniqueSources,
    BRUSH_SOURCE_LOAD_CONCURRENCY,
    async (canonicalSourceUrl) => {
      const requestUrl = getStockBrushRequestUrl(canonicalSourceUrl);
      const stockMetadata = getStockBrushMetadataForSource(canonicalSourceUrl);
      try {
        if (!brushSourceDataCache.has(requestUrl)) {
          const metadataHasDimensions = Boolean(
            stockMetadata && stockMetadata.width > 0 && stockMetadata.height > 0
          );
          const dimensionsPromise = metadataHasDimensions
            ? Promise.resolve({ width: stockMetadata.width, height: stockMetadata.height })
            : getImageDimensions(requestUrl);
          brushSourceDataCache.set(
            requestUrl,
            dimensionsPromise
              .then((dimensions) => ({
                url: requestUrl,
                name: stockMetadata?.name || getBrushSourceFileName(canonicalSourceUrl),
                width: dimensions.width,
                height: dimensions.height,
                originalUrl: canonicalSourceUrl,
                originalWidth: dimensions.width,
                originalHeight: dimensions.height,
                frameCount:
                  stockMetadata?.frameCount || (isGifUrl(canonicalSourceUrl) ? null : 1),
                durationMs: Math.max(0, Number(stockMetadata?.durationMs) || 0),
                animated:
                  stockMetadata?.animated === true || isGifUrl(canonicalSourceUrl),
                opaque: stockMetadata?.opaque === true,
                frameRange: null,
                cropRect: null,
                tags: getStockBrushTagsForSource(canonicalSourceUrl),
                stockAssetRevision: getStockBrushAssetRevisionForSource(canonicalSourceUrl),
                enabled: true,
                weightMode: "normal"
              }))
              .catch((error) => {
                brushSourceDataCache.delete(requestUrl);
                throw error;
              })
          );
        }
        return cloneBrushSourceData(await brushSourceDataCache.get(requestUrl));
      } catch (error) {
        return null;
      }
    }
  );
  return loadedBrushData.filter(Boolean);
}

function refreshExistingBrushFromSourceData(brush, freshBrushData) {
  if (!brush || !freshBrushData) {
    return brush;
  }

  const oldOriginalWidth = getBrushOriginalWidth(brush);
  const oldOriginalHeight = getBrushOriginalHeight(brush);
  const oldOutputWidth = Math.max(1, Number(brush.width) || oldOriginalWidth);
  const oldOutputHeight = Math.max(1, Number(brush.height) || oldOriginalHeight);
  const oldOriginalSource = getBrushPrimarySourceUrl(brush);
  const oldRenderSourceKey = getStockBrushSourceLookupKey(brush.url);
  const originalSourceKey = getStockBrushSourceLookupKey(oldOriginalSource);
  const renderedOriginalSource = Boolean(
    oldRenderSourceKey &&
      originalSourceKey &&
      oldRenderSourceKey === originalSourceKey &&
      !/^(?:blob|data):/i.test(String(brush.url || ""))
  );
  const usedNativeOutputSize = Boolean(
    renderedOriginalSource &&
      !brush.cropRect &&
      Math.round(oldOutputWidth) === Math.round(oldOriginalWidth) &&
      Math.round(oldOutputHeight) === Math.round(oldOriginalHeight)
  );
  const freshOriginalWidth = getBrushOriginalWidth(freshBrushData);
  const freshOriginalHeight = getBrushOriginalHeight(freshBrushData);

  if (brush.cropRect) {
    const widthScale = freshOriginalWidth / oldOriginalWidth;
    const heightScale = freshOriginalHeight / oldOriginalHeight;
    brush.cropRect = normalizeBrushCropRect(
      {
        x: Number(brush.cropRect.x) * widthScale,
        y: Number(brush.cropRect.y) * heightScale,
        width: Number(brush.cropRect.width) * widthScale,
        height: Number(brush.cropRect.height) * heightScale
      },
      freshOriginalWidth,
      freshOriginalHeight
    );
  }

  brush.originalUrl = getBrushPrimarySourceUrl(freshBrushData);
  brush.originalWidth = freshOriginalWidth;
  brush.originalHeight = freshOriginalHeight;
  brush.name = freshBrushData.name || brush.name;
  brush.tags = getBrushTags(freshBrushData);
  brush.stockAssetRevision = freshBrushData.stockAssetRevision || "";
  if (renderedOriginalSource) {
    brush.url = freshBrushData.url;
  }
  if (usedNativeOutputSize) {
    brush.width = freshOriginalWidth;
    brush.height = freshOriginalHeight;
  }
  if (!normalizeBrushFrameCount(brush.frameCount)) {
    brush.frameCount = normalizeBrushFrameCount(freshBrushData.frameCount);
  }
  brush.durationMs = Math.max(0, Number(freshBrushData.durationMs) || 0);
  brush.animated = freshBrushData.animated === true;
  brush.opaque = freshBrushData.opaque === true;
  return brush;
}

async function refreshRestoredStockBrushes(brushes) {
  const revisedSources = Array.from(
    new Set(
      (Array.isArray(brushes) ? brushes : [])
        .filter((brush) => {
          const source = getBrushPrimarySourceUrl(brush);
          const expectedRevision = getStockBrushAssetRevisionForSource(source);
          return Boolean(expectedRevision && brush.stockAssetRevision !== expectedRevision);
        })
        .map(getBrushPrimarySourceUrl)
    )
  );
  if (!revisedSources.length) {
    return 0;
  }

  const refreshedData = await loadBrushSourceData(revisedSources);
  const refreshedBySource = new Map(
    refreshedData.map((brushData) => [getBrushPrimarySourceUrl(brushData), brushData])
  );
  const missingSources = revisedSources.filter((source) => !refreshedBySource.has(source));
  if (missingSources.length) {
    const retriedData = await loadBrushSourceData(missingSources);
    for (const brushData of retriedData) {
      refreshedBySource.set(getBrushPrimarySourceUrl(brushData), brushData);
    }
  }
  let refreshedCount = 0;
  for (const brush of brushes) {
    const freshBrushData = refreshedBySource.get(getBrushPrimarySourceUrl(brush));
    if (!freshBrushData) {
      continue;
    }
    refreshExistingBrushFromSourceData(brush, freshBrushData);
    refreshedCount += 1;
  }
  return refreshedCount;
}

function getBrushPickSourceFromStamp(stamp) {
  if (!(stamp instanceof HTMLImageElement) || !stamp.classList.contains("stamp")) {
    return "";
  }
  const source =
    stamp.dataset.sequenceDisplayedSource ||
    stamp.dataset.sequenceImageCycleSrc ||
    stamp.dataset.sequenceBaseSrc ||
    stamp.dataset.brushUrl ||
    stamp.currentSrc ||
    stamp.getAttribute("src") ||
    "";
  return source && source !== TRANSPARENT_STAMP_SRC
    ? getCanonicalStockBrushSource(source)
    : "";
}

async function loadSingleBrushFromStamp(stamp) {
  const source = getBrushPickSourceFromStamp(stamp);
  if (!source) {
    updateBrushStatus("No canvas image picked.");
    return false;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  const loaded = await loadBrushSourceData([source]);
  if (!loaded.length) {
    updateBrushStatus("Could not load picked image.");
    return false;
  }

  const previousBrushUrls = state.brushes.map((brush) => brush.url);
  const brush = {
    id: state.nextBrushId,
    ...loaded[0],
    enabled: true
  };
  state.nextBrushId += 1;
  state.favoriteReturnState = null;
  state.brushes = [brush];
  resetBrushGalleryForBrushSetChange();
  clearBrushFrameCountJobs();
  setSoloBrushId(brush.id);
  clearActiveStockBrushFolders();
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
  state.pendingBrushGallerySelectionScroll = true;
  updateBrushStatus(`Picked ${brush.name}.`);
  renderBrushGallery();
  renderStockBrushButtons();
  updateEraseCursorGeometry();
  updateBrushCursorPreview();
  scheduleSessionSave();
  return true;
}

async function handleBrushImagePick(event) {
  const stamp = getTopOpaqueStampAtClientPoint(event.clientX, event.clientY, {
    includePointerTransparent: true
  });
  setBrushPickMode(false);
  if (!stamp) {
    updateBrushStatus();
    return;
  }
  await loadSingleBrushFromStamp(stamp);
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
    resetBrushGalleryForBrushSetChange();
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    clearActiveStockBrushFolders();
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

async function browseAllStockBrushFolders(options = {}) {
  if (state.stockBrushLoadingFolderId) {
    return;
  }

  const folders = getOrderedStockBrushFolders().filter((folder) => getStockBrushFiles(folder).length);
  const files = folders.flatMap((folder) => getStockBrushFiles(folder));
  if (!files.length) {
    return;
  }

  const catalogSourceUrls = Array.from(
    new Set(files.map((filePath) => getCanonicalStockBrushSource(encodeStockBrushPath(filePath))))
  );
  const selectedBrushIds = state.selectedBrushIds instanceof Set
    ? state.selectedBrushIds
    : new Set();
  const explicitlyActiveBrushIds = new Set(selectedBrushIds);
  const soloBrush = getSoloBrush();
  if (soloBrush) {
    explicitlyActiveBrushIds.add(soloBrush.id);
  }
  const getExistingBrushPriority = (brush) => {
    if (brush.id === soloBrush?.id) {
      return 3;
    }
    if (selectedBrushIds.has(brush.id)) {
      return 2;
    }
    return brush.enabled ? 1 : 0;
  };
  const existingBrushesBySource = new Map();
  for (const brush of state.brushes) {
    const source = getBrushPrimarySourceUrl(brush);
    if (!source) {
      continue;
    }
    const current = existingBrushesBySource.get(source);
    if (!current || getExistingBrushPriority(brush) > getExistingBrushPriority(current)) {
      existingBrushesBySource.set(source, brush);
    }
  }

  const sourcesToLoad = catalogSourceUrls.filter(
    (source) => {
      const existingBrush = existingBrushesBySource.get(source);
      const expectedRevision = getStockBrushAssetRevisionForSource(source);
      return (
        !existingBrush ||
        Boolean(expectedRevision && existingBrush.stockAssetRevision !== expectedRevision)
      );
    }
  );
  if (state.browsingAllStockBrushes && !sourcesToLoad.length) {
    return;
  }

  if (state.brushCropEditor.open) {
    closeBrushCropModal();
  }

  state.stockBrushLoadingFolderId = "browse-all";
  renderStockBrushButtons();
  updateBrushStatus("Loading all stock brushes to browse...");

  try {
    const loadedBySource = new Map();
    if (sourcesToLoad.length) {
      const loaded = await loadBrushSourceData(sourcesToLoad);
      for (const brushData of loaded) {
        loadedBySource.set(getBrushPrimarySourceUrl(brushData), brushData);
      }
      const missingAfterFirstLoad = sourcesToLoad.filter(
        (source) => !loadedBySource.has(source)
      );
      if (missingAfterFirstLoad.length) {
        const retried = await loadBrushSourceData(missingAfterFirstLoad);
        for (const brushData of retried) {
          loadedBySource.set(getBrushPrimarySourceUrl(brushData), brushData);
        }
      }
    }

    const retainedBrushIds = new Set();
    const stockSourceUrls = new Set(catalogSourceUrls);
    const nextBrushes = catalogSourceUrls.flatMap((source) => {
      const existingBrush = existingBrushesBySource.get(source);
      const freshBrushData = loadedBySource.get(source);
      if (existingBrush) {
        if (freshBrushData) {
          refreshExistingBrushFromSourceData(existingBrush, freshBrushData);
        }
        existingBrush.enabled = explicitlyActiveBrushIds.has(existingBrush.id);
        retainedBrushIds.add(existingBrush.id);
        return [existingBrush];
      }
      if (!freshBrushData) {
        return [];
      }
      return [
        createBrushFromSourceData({
          ...freshBrushData,
          enabled: false
        })
      ];
    });

    for (const brush of state.brushes) {
      const source = getBrushPrimarySourceUrl(brush);
      if (!retainedBrushIds.has(brush.id) && !stockSourceUrls.has(source)) {
        retainedBrushIds.add(brush.id);
        nextBrushes.push(brush);
      }
    }

    const discardedBrushUrls = state.brushes
      .filter((brush) => !retainedBrushIds.has(brush.id))
      .map((brush) => brush.url);
    state.favoriteReturnState = null;
    state.brushes = nextBrushes;
    if (!options.preserveGalleryState) {
      resetBrushGalleryForBrushSetChange();
    }
    clearBrushFrameCountJobs();
    clearActiveStockBrushFolders();
    clearActiveCustomBrushPreset();
    state.browsingAllStockBrushes = true;

    const brushIds = new Set(state.brushes.map((brush) => brush.id));
    if (!brushIds.has(state.soloBrushId)) {
      state.soloBrushId = null;
    }
    state.selectedBrushIds = new Set(
      Array.from(selectedBrushIds).filter((brushId) => brushIds.has(brushId))
    );
    for (const oldUrl of discardedBrushUrls) {
      maybeReleaseObjectUrl(oldUrl);
    }

    const unresolvedSourceCount = catalogSourceUrls.reduce((count, source) => {
      const existingBrush = existingBrushesBySource.get(source);
      const expectedRevision = getStockBrushAssetRevisionForSource(source);
      const existingBrushIsCurrent = Boolean(
        existingBrush && (!expectedRevision || existingBrush.stockAssetRevision === expectedRevision)
      );
      return count + (existingBrushIsCurrent || loadedBySource.has(source) ? 0 : 1);
    }, 0);
    if (unresolvedSourceCount) {
      updateBrushStatus(
        `Browsing ${state.brushes.length.toLocaleString()} brushes; ${unresolvedSourceCount.toLocaleString()} could not load.`
      );
    } else {
      updateBrushStatus();
    }
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
    const catalogSourceUrls = Array.from(
      new Set(files.map((filePath) => getCanonicalStockBrushSource(encodeStockBrushPath(filePath))))
    );
    const loadedBySource = new Map();
    const loaded = await loadBrushSourceData(catalogSourceUrls);
    for (const brushData of loaded) {
      loadedBySource.set(getBrushPrimarySourceUrl(brushData), brushData);
    }
    const missingAfterFirstLoad = catalogSourceUrls.filter(
      (source) => !loadedBySource.has(source)
    );
    if (missingAfterFirstLoad.length) {
      const retried = await loadBrushSourceData(missingAfterFirstLoad);
      for (const brushData of retried) {
        loadedBySource.set(getBrushPrimarySourceUrl(brushData), brushData);
      }
    }
    const missingSourceCount = catalogSourceUrls.reduce(
      (count, source) => count + (loadedBySource.has(source) ? 0 : 1),
      0
    );
    if (missingSourceCount) {
      updateBrushStatus(
        `Could not load ${missingSourceCount.toLocaleString()} stock brush${missingSourceCount === 1 ? "" : "es"}. Try again.`
      );
      return;
    }
    const completeCatalog = catalogSourceUrls.map((source) => loadedBySource.get(source));

    const previousBrushUrls = state.brushes.map((brush) => brush.url);
    state.brushes = completeCatalog.map((brushData) => {
      const brush = {
        id: state.nextBrushId,
        ...brushData,
        enabled: true
      };
      state.nextBrushId += 1;
      return brush;
    });
    resetBrushGalleryForBrushSetChange();
    clearBrushFrameCountJobs();
    state.soloBrushId = null;
    clearSelectedBrushes();
    setActiveStockBrushFolders(folders.map((folder) => folder.id), "all");
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

function removeStockBrushFolderFromActiveSelection(folderId) {
  if (state.stockBrushLoadingFolderId) {
    return false;
  }

  const folder = getStockBrushFolderById(folderId);
  if (!folder) {
    return false;
  }

  const activeFolderIds = getActiveStockBrushFolderIdSet();
  if (!activeFolderIds.has(folder.id) || activeFolderIds.size <= 1) {
    return false;
  }

  const folderSourceUrls = new Set(getStockBrushFolderSourceUrls(folder));
  const removedUrls = [];
  state.brushes = state.brushes.filter((brush) => {
    if (folderSourceUrls.has(getBrushPrimarySourceUrl(brush))) {
      removedUrls.push(brush.url);
      return false;
    }
    return true;
  });

  activeFolderIds.delete(folder.id);
  if (activeFolderIds.size) {
    setActiveStockBrushFolders(
      Array.from(activeFolderIds),
      activeFolderIds.size > 1 ? "multi" : "single"
    );
  } else {
    clearActiveStockBrushFolders();
  }
  refreshBrushDataAfterLoad(removedUrls);
  return true;
}

function unloadBrushDataSelection() {
  if (!state.brushes.length) {
    resetBrushGalleryForBrushSetChange();
    clearActiveStockBrushFolders();
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
  resetBrushGalleryForBrushSetChange();
  clearBrushFrameCountJobs();
  state.soloBrushId = null;
  clearSelectedBrushes();
  clearActiveStockBrushFolders();
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
        tags: [],
        enabled: true,
        weightMode: "normal"
      });
      state.nextBrushId += 1;
    } catch (error) {
      // Skip unreadable files and continue loading the rest.
    }
  }

  state.brushes = loaded;
  resetBrushGalleryForBrushSetChange();
  clearBrushFrameCountJobs();
  state.soloBrushId = null;
  clearSelectedBrushes();
  clearActiveStockBrushFolders();
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
  const stamps = getSceneRendererStampsInOrder();
  for (let index = 0; index < stamps.length; index += 1) {
    worldOrder.set(stamps[index], index);
  }
  const strokeOrder = new Map();
  const stampOrder = new Map();
  for (let strokeIndex = 0; strokeIndex < state.strokes.length; strokeIndex += 1) {
    const stroke = state.strokes[strokeIndex];
    strokeOrder.set(stroke, strokeIndex);
    for (let stampIndex = 0; stampIndex < stroke.elements.length; stampIndex += 1) {
      stampOrder.set(stroke.elements[stampIndex], stampIndex);
    }
  }
  const removalContext = {
    records: [],
    worldOrder,
    strokeOrder,
    stampOrder
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
  syncViewportPointerCursorClasses();
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
  syncViewportPointerCursorClasses();
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
  syncViewportPointerCursorClasses();
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
  syncViewportPointerCursorClasses();
  scheduleSceneRendererEvaluation();
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

  syncViewportPointerCursorClasses();
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

  if (!draft.dragging && !draft.fromPending) {
    draft.pointerId = null;
    draft.currentX = draft.anchorX;
    draft.currentY = draft.anchorY;
    hideShapePreview();
    syncViewportPointerCursorClasses();
    return;
  }

  const { mode, anchorX, anchorY, currentX, currentY } = draft;
  state.shapeDraft = null;
  hideShapePreview();
  syncViewportPointerCursorClasses();
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
  if (state.brushPickMode) {
    void handleBrushImagePick(event);
    return;
  }

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
  updateEditLayerHoverCursor(event.clientX, event.clientY);

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
    if (state.sceneRendererActive || state.sceneRendererPreparing) {
      deactivateSceneRenderer();
    }
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
  if (!state.eraseMode) {
    scheduleSceneRendererEvaluation();
  }
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

function commitExportResolutionInput(axis, input) {
  if (!input || state.exportTask || String(input.value).trim() === "") {
    return;
  }
  const beforeSetup = captureCurrentExportSetupSnapshot();
  setExportResolutionFromInput(axis, input.value);
  pushExportCropHistoryStep(beforeSetup, captureCurrentExportSetupSnapshot(), {
    requireBoundsChange: true
  });
}

function onExportResolutionKeyDown(event, axis, input) {
  if (event.key !== "Enter") {
    return;
  }
  event.preventDefault();
  commitExportResolutionInput(axis, input);
  input.blur();
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
    const clickedNameElement = event.target.closest(".edit-layer-name");
    if (clickedNameElement && event.detail >= 2) {
      const nameRow = clickedNameElement.closest(".edit-layer-row");
      const nameStroke = getStrokeById(nameRow?.dataset.strokeId);
      if (nameStroke) {
        event.preventDefault();
        event.stopPropagation();
        state.selectedEditLayerId = nameStroke.id;
        startLayerNameEdit(nameStroke, clickedNameElement);
      }
      return;
    }

    const row = event.target.closest(".edit-layer-row");
    const sequenceRow = event.target.closest(".edit-layer-sequence-row");
    const sequenceSettings = event.target.closest(".edit-layer-sequence-settings");
    const sequenceAddRow = event.target.closest(".edit-layer-sequence-add-row");
    const blendRow = event.target.closest(".edit-layer-blend-row");
    const layerPropertyControls = event.target.closest(".edit-layer-property-controls");
    const strokeId = Number(
      row?.dataset.strokeId ||
        sequenceRow?.dataset.strokeId ||
        sequenceSettings?.dataset.strokeId ||
        sequenceAddRow?.dataset.strokeId ||
        blendRow?.dataset.strokeId ||
        layerPropertyControls?.dataset.strokeId
    );
    const stroke = getStrokeById(strokeId);
    if (!stroke) {
      return;
    }

    const blendButton = event.target.closest(".edit-layer-blend-button");
    if (blendButton) {
      event.preventDefault();
      const menu = blendButton.closest(".edit-layer-blend-menu");
      if (menu?.classList.contains("is-open")) {
        closeLayerBlendMenu(menu, true);
      } else {
        openLayerBlendMenu(menu, stroke);
      }
      state.selectedEditLayerId = stroke.id;
      return;
    }

    const blendOption = event.target.closest(".edit-layer-blend-option");
    if (blendOption) {
      event.preventDefault();
      const menu = blendOption.closest(".edit-layer-blend-menu");
      const nextBlendMode = normalizeLayerBlendMode(blendOption.dataset.blendMode);
      setLayerBlendMode(stroke, nextBlendMode);
      if (menu) {
        menu.dataset.originalBlendMode = nextBlendMode;
        updateLayerBlendMenuSelection(menu, nextBlendMode);
        closeLayerBlendMenu(menu, false);
      }
      state.selectedEditLayerId = stroke.id;
      scheduleSessionSave();
      return;
    }

    const sequenceButton = event.target.closest(".edit-layer-sequence-button");
    if (sequenceButton) {
      event.preventDefault();
      stroke.sequenceOpen = !stroke.sequenceOpen;
      markStrokeSerializationDirty(stroke);
      selectEditLayer(stroke.id);
      renderEditLayers();
      scheduleSessionSave();
      return;
    }

    const sequenceEnabledButton = event.target.closest(".edit-layer-sequence-enable-button");
    if (sequenceEnabledButton) {
      event.preventDefault();
      const nextEnabled = !isLayerSequenceEnabled(stroke);
      stroke.sequenceUserDisabled = !nextEnabled;
      stroke.sequenceEnabled = nextEnabled;
      refreshStrokeSequenceEffect(stroke);
      selectEditLayer(stroke.id);
      renderEditLayers();
      scheduleSessionSave();
      return;
    }

    const sequenceAddButton = event.target.closest(".edit-layer-sequence-add-button");
    if (sequenceAddButton) {
      event.preventDefault();
      if (addLayerSequenceSlot(stroke)) {
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
      if (removeLayerSequenceSlot(stroke, slotIndex)) {
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

  editLayerList.addEventListener("dblclick", (event) => {
    const nameElement = event.target.closest(".edit-layer-name");
    if (!nameElement || nameElement.querySelector(".edit-layer-name-input")) {
      return;
    }
    const row = nameElement.closest(".edit-layer-row");
    const stroke = state.strokeById.get(Number(row?.dataset.strokeId));
    if (!stroke) {
      return;
    }
    event.preventDefault();
    event.stopPropagation();
    state.selectedEditLayerId = stroke.id;
    startLayerNameEdit(stroke, nameElement);
  });

  editLayerList.addEventListener("change", (event) => {
    const freezeInput = event.target.closest(".edit-layer-freeze-input");
    if (freezeInput) {
      const panel = freezeInput.closest(".edit-layer-property-controls");
      const stroke = getStrokeById(panel?.dataset.strokeId);
      if (!stroke) {
        return;
      }
      stroke.animationPaused = Boolean(freezeInput.checked);
      applyStrokeAnimationPaused(stroke);
      selectEditLayer(stroke.id);
      scheduleSessionSave();
      return;
    }

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
    stroke.sequenceConfigured = true;
    stroke.sequenceEnabled = true;
    stroke.sequenceUserDisabled = false;
    refreshStrokeSequenceEffect(stroke);
    selectEditLayer(stroke.id);
    renderEditLayers();
    scheduleSessionSave();
  });

  editLayerList.addEventListener("input", (event) => {
    const layerInput = event.target.closest(".edit-layer-property-input");
    if (layerInput) {
      const panel = layerInput.closest(".edit-layer-property-controls");
      const stroke = getStrokeById(panel?.dataset.strokeId);
      if (!stroke) {
        return;
      }
      const key = layerInput.dataset.layerSetting || "";
      setLayerControlValue(stroke, key, layerInput.value);
      const valueLabel = layerInput.parentElement?.querySelector(".edit-layer-property-value");
      if (valueLabel) {
        valueLabel.textContent = getLayerControlDisplayValue(stroke, key);
      }
      scheduleSessionSave();
      return;
    }

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
      scheduleStrokeSequenceEffectRefresh(stroke);
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
    scheduleStrokeSequenceEffectRefresh(stroke);
    const valueLabel = settingInput.parentElement?.querySelector(".edit-layer-sequence-setting-value");
    if (valueLabel) {
      const suffix = valueLabel.textContent.endsWith("ms")
        ? "ms"
        : valueLabel.textContent.endsWith("%")
        ? "%"
        : valueLabel.textContent.endsWith("px")
        ? "px"
        : "";
      valueLabel.textContent = `${getSequenceSettingInputValue(settingInput)}${suffix}`;
    }
    scheduleSessionSave();
  });

  editLayerList.addEventListener("pointerover", (event) => {
    const blendOption = event.target.closest(".edit-layer-blend-option");
    if (!blendOption) {
      return;
    }
    const menu = blendOption.closest(".edit-layer-blend-menu");
    const stroke = getStrokeById(menu?.dataset.strokeId);
    if (!menu || !stroke || !menu.classList.contains("is-open")) {
      return;
    }
    const nextBlendMode = normalizeLayerBlendMode(blendOption.dataset.blendMode);
    setLayerBlendMode(stroke, nextBlendMode);
    for (const option of menu.querySelectorAll(".edit-layer-blend-option.is-preview")) {
      option.classList.remove("is-preview");
    }
    blendOption.classList.add("is-preview");
  });

  editLayerList.addEventListener("pointerdown", (event) => {
    const nameElement = event.target.closest(".edit-layer-name");
    if (nameElement && event.button === 0 && event.detail >= 2) {
      const row = nameElement.closest(".edit-layer-row");
      const stroke = getStrokeById(row?.dataset.strokeId);
      if (stroke) {
        event.preventDefault();
        event.stopPropagation();
        state.selectedEditLayerId = stroke.id;
        startLayerNameEdit(stroke, nameElement);
      }
      return;
    }
	    if (
	      event.button !== 0 ||
      event.target.closest(".edit-layer-eye-button") ||
      event.target.closest(".edit-layer-sequence-button") ||
      event.target.closest(".edit-layer-sequence-enable-button") ||
      event.target.closest(".edit-layer-sequence-row") ||
      event.target.closest(".edit-layer-blend-row") ||
      event.target.closest(".edit-layer-property-controls") ||
      event.target.closest(".edit-layer-name-input") ||
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
document.addEventListener("click", (event) => {
  if (!event.target.closest(".edit-layer-blend-menu")) {
    closeAllLayerBlendMenus(null, true);
  }
});
if (stockBrushButtons) {
  stockBrushButtons.addEventListener("click", (event) => {
    const button = event.target.closest(".stock-brush-button");
    if (!button || button.disabled) {
      return;
    }
    event.preventDefault();
    void loadStockBrushFolder(button.dataset.stockBrushFolderId || "", {
      additive: (event.ctrlKey || event.metaKey) && !state.browsingAllStockBrushes
    });
  });
  stockBrushButtons.addEventListener("contextmenu", (event) => {
    const button = event.target.closest(".stock-brush-button");
    if (!button || button.disabled) {
      return;
    }
    if (removeStockBrushFolderFromActiveSelection(button.dataset.stockBrushFolderId || "")) {
      event.preventDefault();
    }
  });
}
if (browseAllStockBrushesButton) {
  browseAllStockBrushesButton.addEventListener("click", (event) => {
    event.preventDefault();
    void browseAllStockBrushFolders();
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
if (brushImagePickerButton) {
  brushImagePickerButton.addEventListener("click", (event) => {
    event.preventDefault();
    setBrushPickMode(!state.brushPickMode);
  });
}
for (const presetContainer of [drawingBrushPresetButtons, brushesBrushPresetButtons]) {
  if (presetContainer) {
    presetContainer.addEventListener("click", onCustomBrushPresetClick);
    presetContainer.addEventListener("dragover", onCustomBrushPresetDragOver);
    presetContainer.addEventListener("drop", onCustomBrushPresetDrop);
  }
}
if (brushGalleryPreviousPageButton) {
  brushGalleryPreviousPageButton.addEventListener("click", () => {
    setBrushGalleryPage(state.brushGalleryPage - 1);
  });
}
if (brushGalleryNextPageButton) {
  brushGalleryNextPageButton.addEventListener("click", () => {
    setBrushGalleryPage(state.brushGalleryPage + 1);
  });
}
if (brushSortSelect) {
  brushSortSelect.addEventListener("change", () => {
    const nextSort = normalizeBrushGallerySort(brushSortSelect.value);
    if (nextSort === "random") {
      state.brushGalleryRandomSeed = createBrushGalleryRandomSeed();
    }
    state.brushGallerySort = nextSort;
    resetBrushGalleryPage();
    renderBrushGallery();
    brushGallery.scrollTop = 0;
    scheduleSessionSave();
  });
}
if (brushGallerySearchInput) {
  brushGallerySearchInput.addEventListener("input", () => {
    const nextSearch = normalizeBrushGallerySearch(brushGallerySearchInput.value);
    if (nextSearch === state.brushGallerySearch) {
      return;
    }
    setBrushTagMenuOpen(false);
    state.brushGallerySearch = nextSearch;
    resetBrushGalleryPage();
    renderBrushGallery();
    brushGallery.scrollTop = 0;
    scheduleSessionSave();
  });
}
if (brushTagMenuButton) {
  brushTagMenuButton.addEventListener("click", (event) => {
    event.preventDefault();
    setBrushTagMenuOpen(!state.brushTagMenuOpen);
  });
  brushTagMenuButton.addEventListener("keydown", (event) => {
    if (event.key !== "ArrowDown" && event.key !== "ArrowUp") {
      return;
    }
    event.preventDefault();
    setBrushTagMenuOpen(true);
    const items = Array.from(brushTagMenu?.querySelectorAll(".brush-tag-menu-item") || []);
    const item = event.key === "ArrowUp" ? items[items.length - 1] : items[0];
    item?.focus();
  });
}
if (brushTagMenu) {
  brushTagMenu.addEventListener("click", (event) => {
    const button = event.target.closest(".brush-tag-menu-item");
    if (!button || !brushTagMenu.contains(button)) {
      return;
    }
    event.preventDefault();
    applyBrushTagSearch(button.dataset.brushTag || "");
  });
  brushTagMenu.addEventListener("keydown", (event) => {
    if (!["ArrowDown", "ArrowUp", "Home", "End"].includes(event.key)) {
      return;
    }
    const items = Array.from(brushTagMenu.querySelectorAll(".brush-tag-menu-item"));
    if (!items.length) {
      return;
    }
    event.preventDefault();
    const activeIndex = Math.max(0, items.indexOf(document.activeElement));
    let nextIndex = activeIndex;
    if (event.key === "ArrowDown") {
      nextIndex = (activeIndex + 1) % items.length;
    } else if (event.key === "ArrowUp") {
      nextIndex = (activeIndex - 1 + items.length) % items.length;
    } else if (event.key === "Home") {
      nextIndex = 0;
    } else if (event.key === "End") {
      nextIndex = items.length - 1;
    }
    items[nextIndex]?.focus();
  });
}
if (brushSearchControls) {
  brushSearchControls.addEventListener("focusout", (event) => {
    const nextTarget = event.relatedTarget;
    if (
      state.brushTagMenuOpen &&
      (!(nextTarget instanceof Node) || !brushSearchControls.contains(nextTarget))
    ) {
      setBrushTagMenuOpen(false);
    }
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
if (randomSizeToggle) {
  randomSizeToggle.addEventListener("change", () => {
    state.randomSizeEnabled = randomSizeToggle.checked;
    if (state.randomSizeEnabled) {
      initializeRandomSizeRangeFromCurrent();
    }
    updateConsistentModeUI();
    updateEraseCursorGeometry();
    updateBrushCursorPreview();
    scheduleSessionSave();
  });
}
if (randomSizeMinSlider) {
  randomSizeMinSlider.addEventListener("input", readRandomSizeSliders);
}
if (randomSizeMaxSlider) {
  randomSizeMaxSlider.addEventListener("input", readRandomSizeSliders);
}
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
    setDrawMode(getDrawModeFromButtonClick(button.dataset.drawMode || "pencil"));
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
    updateGifPauseButtonUI();
    updateExportOverlayGeometry();
    scheduleSessionSave();
  });
}
if (exportGuidelinesToggle) {
  exportGuidelinesToggle.addEventListener("change", () => {
    state.exportGuidelinesEnabled = exportGuidelinesToggle.checked;
    updateExportGuidelinesUI();
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
if (brushCropZoomInput) {
  brushCropZoomInput.addEventListener("input", () => {
    setBrushCropZoomPercent(brushCropZoomInput.value);
  });
}
if (brushCropZoomOutButton) {
  brushCropZoomOutButton.addEventListener("click", () => {
    setBrushCropZoomPercent(
      Number(state.brushCropEditor.zoomPercent) - BRUSH_CROP_ZOOM_STEP_PERCENT
    );
  });
}
if (brushCropZoomInButton) {
  brushCropZoomInButton.addEventListener("click", () => {
    setBrushCropZoomPercent(
      Number(state.brushCropEditor.zoomPercent) + BRUSH_CROP_ZOOM_STEP_PERCENT
    );
  });
}
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
if (exportSequencePrewarmInput) {
  exportSequencePrewarmInput.addEventListener("input", () => {
    const value = String(exportSequencePrewarmInput.value || "").trim();
    state.exportSequencePrewarmSeconds = value
      ? clamp(Number(value) || 0, 0, 300)
      : 0;
    if (value && Number(exportSequencePrewarmInput.value) !== state.exportSequencePrewarmSeconds) {
      exportSequencePrewarmInput.value = String(state.exportSequencePrewarmSeconds);
    }
    updateExportAnimationUI();
    scheduleSessionSave();
  });
}
if (exportGifSizeLimitToggle) {
  exportGifSizeLimitToggle.addEventListener("change", () => {
    state.exportGifSizeLimitEnabled = exportGifSizeLimitToggle.checked;
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
exportWidthInput.addEventListener("keydown", (event) => {
  onExportResolutionKeyDown(event, "width", exportWidthInput);
});
exportWidthInput.addEventListener("change", () => {
  commitExportResolutionInput("width", exportWidthInput);
});
exportHeightInput.addEventListener("keydown", (event) => {
  onExportResolutionKeyDown(event, "height", exportHeightInput);
});
exportHeightInput.addEventListener("change", () => {
  commitExportResolutionInput("height", exportHeightInput);
});
if (exportSidebarWidthInput) {
  exportSidebarWidthInput.addEventListener("keydown", (event) => {
    onExportResolutionKeyDown(event, "width", exportSidebarWidthInput);
  });
  exportSidebarWidthInput.addEventListener("change", () => {
    commitExportResolutionInput("width", exportSidebarWidthInput);
  });
}
if (exportSidebarHeightInput) {
  exportSidebarHeightInput.addEventListener("keydown", (event) => {
    onExportResolutionKeyDown(event, "height", exportSidebarHeightInput);
  });
  exportSidebarHeightInput.addEventListener("change", () => {
    commitExportResolutionInput("height", exportSidebarHeightInput);
  });
}
if (exportResolutionLockButton) {
  exportResolutionLockButton.addEventListener("click", (event) => {
    event.preventDefault();
    toggleExportResolutionLock();
  });
}
if (exportSidebarResolutionLockButton) {
  exportSidebarResolutionLockButton.addEventListener("click", (event) => {
    event.preventDefault();
    toggleExportResolutionLock();
  });
}
exportWidthInput.addEventListener("blur", () => {
  commitExportResolutionInput("width", exportWidthInput);
});
exportHeightInput.addEventListener("blur", () => {
  commitExportResolutionInput("height", exportHeightInput);
});
if (exportSidebarWidthInput) {
  exportSidebarWidthInput.addEventListener("blur", () => {
    commitExportResolutionInput("width", exportSidebarWidthInput);
  });
}
if (exportSidebarHeightInput) {
  exportSidebarHeightInput.addEventListener("blur", () => {
    commitExportResolutionInput("height", exportSidebarHeightInput);
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
document.addEventListener("pointerdown", (event) => {
  if (!state.brushTagMenuOpen || !brushSearchControls) {
    return;
  }
  const target = event.target;
  if (target instanceof Node && brushSearchControls.contains(target)) {
    return;
  }
  setBrushTagMenuOpen(false);
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
  if (event.key === "Escape" && state.brushTagMenuOpen) {
    event.preventDefault();
    setBrushTagMenuOpen(false);
    brushTagMenuButton?.focus();
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
    if (state.placementTask || state.exportTask) {
      event.preventDefault();
      return;
    }
    event.preventDefault();
    if (state.exportMode) {
      if (state.exportDrag) {
        if (event.shiftKey) {
          return;
        }
        stopExportSelectionDrag(state.exportDrag.pointerId);
      }
      if (event.shiftKey) {
        redoExportCropAdjustment();
      } else {
        undoExportCropAdjustment();
      }
      return;
    }
    if (state.editLayerMove) {
      if (event.shiftKey) {
        return;
      }
      stopEditLayerMove(state.editLayerMove.pointerId);
    }
    if (event.shiftKey) {
      redoKeyboardHistoryAction();
    } else {
      undoKeyboardHistoryAction();
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
  updateEditLayerHoverCursor(event.clientX, event.clientY);
});
viewport.addEventListener("pointerleave", () => {
  state.pointerInViewport = false;
  resetCursorTrailAnchor();
  updateEraseCursorVisibility();
  hideBrushCursorPreview();
  viewport.classList.remove("is-edit-layer-clickable");
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
window.addEventListener("pageshow", () => {
  lastLifecycleFlushRevision = -1;
});
window.addEventListener("resize", () => {
  if (state.sceneRendererPreparing) {
    noteSceneRendererMutation();
  }
  resizeSceneRenderer();
  updateEditLayerDeleteDropzonePosition();
  updateGifPauseButtonPosition();
  if (state.exportMode) {
    updateExportOverlayGeometry();
  }
  if (state.brushCropEditor.open) {
    renderBrushCropModal();
    centerBrushCropSelectionInPreview();
  }
});
controlsPanel.addEventListener("scroll", () => {
  if (state.editLayerDrag) {
    updateEditLayerDeleteDropzonePosition();
  }
});
document.addEventListener("visibilitychange", () => {
  if (document.visibilityState === "hidden") {
    const now = performance.now();
    for (const stroke of state.strokes) {
      setStrokeSequenceClockPaused(stroke, true, now);
    }
    stopLayerSequenceLoop();
    if (sceneRendererInitialized && (state.sceneRendererActive || state.sceneRendererPreparing)) {
      postSceneRendererMessage("pause", { paused: true, now });
    }
    flushSessionSaveNow();
    return;
  }
  const now = performance.now();
  for (const stroke of state.strokes) {
    setStrokeSequenceClockPaused(
      stroke,
      Boolean(state.gifAnimationsPaused || stroke.animationPaused),
      now
    );
  }
  if (sceneRendererInitialized && state.sceneRendererActive) {
    resizeSceneRenderer();
    syncSceneRendererCamera();
    postSceneRendererMessage("pause", { paused: false, now });
  } else {
    scheduleSceneRendererEvaluation();
  }
  refreshLayerSequenceLoop();
});
gifPauseObserver.observe(document.body, { childList: true, subtree: true });

async function initializeApp() {
  loadFavoriteBrushSources();
  loadCustomBrushPresetSources();
  const restored = await restoreSessionState();
  if (restored) {
    updateFavoriteBrushButtons();
    refreshLayerSequenceLoop();
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
  refreshLayerSequenceLoop();
}

void initializeApp();
