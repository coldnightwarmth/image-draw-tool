(() => {
  "use strict";

  const GENERATOR_ASSET_REVISION = "20260911-random-floor-v1";
  const CANVAS_MIN_SIZE = 320;
  const CANVAS_MAX_SIZE = 2400;
  const DEFAULT_WIDTH = 1200;
  const DEFAULT_HEIGHT = 800;
  const DEFAULT_COUNT = 120;
  const MIN_RANDOMIZED_COUNT = 5;
  const MAX_GENERATED_COUNT = 300;
  const DEFAULT_MARGIN = 0;
  const MAX_MARGIN_FRACTION = 0.45;
  const MODE_ORDER = ["line", "spray", "box", "scatter"];
  const SEQUENCE_EFFECTS = [
    "show-hide",
    "move",
    "rotate",
    "scale",
    "color-cycle",
    "image-cycle",
    "pixelate",
    "blur"
  ];
  const SEQUENCE_TIMINGS = ["pulse", "wave", "step", "random", "all", "grouped"];
  const SEQUENCE_GROUPED_EXCLUSIONS = new Set(["show-hide", "color-cycle", "image-cycle"]);
  const SAMPLED_GEOMETRY_KEYS = [
    "sampledSpacing",
    "sampledLineLength",
    "sampledLineAngle",
    "sampledSpraySpread",
    "sampledBoxWidth",
    "sampledBoxHeight"
  ];
  const SEQUENCE_RANDOM_SEED_MASK = 0x71e5c3a9;
  const GENERATION_CONTROL_RANDOM_SEED_MASK = 0x3d4a91f7;
  const BOOKMARK_DATABASE_NAME = "image-draw-generator-bookmarks";
  const BOOKMARK_DATABASE_VERSION = 1;
  const BOOKMARK_STORE_NAME = "compositions";
  const BOOKMARK_SCHEMA_VERSION = 1;
  const BOOKMARK_BACKUP_FORMAT = "image-draw-generator-bookmarks";
  const BOOKMARK_BACKUP_VERSION = 1;
  const BOOKMARK_BACKUP_MAX_BYTES = 250 * 1024 * 1024;
  const BOOKMARK_THUMBNAIL_MAX_BYTES = 8 * 1024 * 1024;
  const ACTIVE_SESSION_RECORD_ID = "__active-generator-session__";
  const ACTIVE_SESSION_RECORD_TYPE = "active-session";
  const ACTIVE_SESSION_SAVE_DELAY_MS = 120;
  const MAX_BOOKMARKS = 500;
  const MAX_HISTORY_ACTIONS = 30;
  const DYNAMIC_UPDATE_DELAY_MS = 120;
  const EXPORT_RASTER_PROTOCOL = "brush-export-raster";
  const EXPORT_RASTER_VERSION = 1;
  const EXPORT_RASTER_WORKER_URL = new URL(
    `../export-raster-worker.js?v=${GENERATOR_ASSET_REVISION}`,
    document.baseURI
  ).href;
  const EXPORT_MP4_MUXER_URL = new URL(
    `./vendor/mp4-muxer.mjs?v=${GENERATOR_ASSET_REVISION}`,
    document.baseURI
  ).href;
  const EXPORT_STARTUP_TIMEOUT_MS = 8000;
  const EXPORT_PREPARE_TIMEOUT_MS = 180000;
  const EXPORT_FRAME_TIMEOUT_MS = 60000;
  const EXPORT_FRAME_INTERVAL_MS = 50;
  const EXPORT_BLUR_MIN_FRAME_INTERVAL_MS = 30;
  const EXPORT_BLUR_TARGET_SAMPLES_PER_CYCLE = 24;
  const EXPORT_SOURCE_FRAME_INTERVAL_MS = 50;
  const PIXELATE_PREVIEW_INTERVAL_MS = 50;
  const EXPORT_LOOP_MIN_MS = 2500;
  const EXPORT_LOOP_MAX_MS = 6000;
  const EXPORT_MP4_DURATION_MS = 6000;
  const EXPORT_MP4_FRAME_RATE = 30;
  const EXPORT_MP4_CODEC = "avc1.420033";
  const byId = (id) => document.getElementById(id);
  const elements = {
    body: document.body,
    controls: byId("controls"),
    controlsMain: byId("generatorControlsMain"),
    bookmarksPanel: byId("generatorBookmarksPanel"),
    bookmarkGalleryMode: byId("generatorBookmarkGalleryModeButton"),
    sidebarToggle: byId("sidebarToggleButton"),
    stageArea: byId("generatorStageArea"),
    canvasFrame: byId("generatorCanvasFrame"),
    canvas: byId("generatorCanvas"),
    composition: byId("generatorComposition"),
    marginOverlay: byId("generatorMarginOverlay"),
    emptyState: byId("generatorEmptyState"),
    dimensionBadge: byId("generatorDimensionBadge"),
    canvasMeta: byId("generatorCanvasMeta"),
    status: byId("generatorStatus"),
    catalogCount: byId("generatorCatalogCount"),
    sourceHint: byId("generatorSourceHint"),
    categoryTab: byId("generatorCategoryTab"),
    tagTab: byId("generatorTagTab"),
    categoryPanel: byId("generatorCategoryPanel"),
    tagPanel: byId("generatorTagPanel"),
    categoryList: byId("generatorCategoryList"),
    tagList: byId("generatorTagList"),
    categorySelectionCount: byId("generatorCategorySelectionCount"),
    tagSelectionCount: byId("generatorTagSelectionCount"),
    width: byId("generatorCanvasWidthInput"),
    height: byId("generatorCanvasHeightInput"),
    margin: byId("generatorMarginSlider"),
    marginValue: byId("generatorMarginValue"),
    marginRandom: byId("generatorMarginRandomToggle"),
    marginModeRandom: byId("generatorMarginModeRandomToggle"),
    marginHint: byId("generatorMarginHint"),
    cropInspect: byId("generatorCropInspectButton"),
    cropInspectStatus: byId("generatorCropInspectStatus"),
    count: byId("generatorCountSlider"),
    countValue: byId("generatorCountValue"),
    countRandom: byId("generatorCountRandomToggle"),
    generate: byId("generatorGenerateButton"),
    backgroundOnly: byId("generatorBackgroundButton"),
    undo: byId("generatorUndoButton"),
    randomizeAll: byId("generatorRandomizeAllToggle"),
    sequenceEnabled: byId("generatorSequenceEnabledToggle"),
    sequenceEffectsRandom: byId("generatorSequenceEffectsRandomToggle"),
    sequenceStateLabel: byId("generatorSequenceStateLabel"),
    sequenceBody: document.querySelector(".generator-sequence-body"),
    sequenceHint: byId("generatorSequenceHint"),
    sequencePause: byId("generatorSequencePauseButton"),
    bookmark: byId("generatorBookmarkButton"),
    downloadWebp: byId("generatorDownloadWebpButton"),
    downloadMp4: byId("generatorDownloadMp4Button"),
    exportCancel: byId("generatorExportCancelButton"),
    exportProgress: byId("generatorExportProgress"),
    exportProgressBar: byId("generatorExportProgressBar"),
    actionStatus: byId("generatorActionStatus"),
    bookmarkCount: byId("generatorBookmarkCount"),
    bookmarkGallery: byId("generatorBookmarkGallery"),
    bookmarkEmpty: byId("generatorBookmarkEmpty"),
    protectBookmarks: byId("generatorProtectBookmarksButton"),
    backupBookmarks: byId("generatorBackupBookmarksButton"),
    restoreBookmarksButton: byId("generatorRestoreBookmarksButton"),
    restoreBookmarks: byId("generatorRestoreBookmarksInput"),
    bookmarkStorageStatus: byId("generatorBookmarkStorageStatus"),
    tintColor: byId("generatorTintColorInput"),
    boxStyle: byId("generatorBoxStyleSelect"),
    backgroundColor: byId("generatorBackgroundColorInput")
  };

  const SINGLE_RANGE_OUTPUTS = [
    ["generatorCountSlider", "generatorCountValue", ""],
    ["generatorMarginSlider", "generatorMarginValue", "px"]
  ].map(([inputId, outputId, suffix]) => ({
    input: byId(inputId),
    output: byId(outputId),
    suffix
  }));

  const RANDOM_RANGE_CONTROLS = [
    ["size", "generatorSizeSlider", "generatorSizeRandomMinSlider", "generatorSizeRandomMaxSlider", "generatorSizeValue", "px"],
    ["spacing", "generatorSpacingSlider", "generatorSpacingRandomMinSlider", "generatorSpacingRandomMaxSlider", "generatorSpacingValue", "px"],
    ["rotation", "generatorRotationSlider", "generatorRotationRandomMinSlider", "generatorRotationRandomMaxSlider", "generatorRotationValue", "°"],
    ["opacity", "generatorOpacitySlider", "generatorOpacityRandomMinSlider", "generatorOpacityRandomMaxSlider", "generatorOpacityValue", "%"],
    ["tint", "generatorTintAmountSlider", "generatorTintAmountRandomMinSlider", "generatorTintAmountRandomMaxSlider", "generatorTintAmountValue", "%"],
    ["spraySpread", "generatorSpraySpreadSlider", "generatorSpraySpreadRandomMinSlider", "generatorSpraySpreadRandomMaxSlider", "generatorSpraySpreadValue", "px"],
    ["lineAngle", "generatorLineAngleSlider", "generatorLineAngleRandomMinSlider", "generatorLineAngleRandomMaxSlider", "generatorLineAngleValue", "°"],
    ["lineLength", "generatorLineLengthSlider", "generatorLineLengthRandomMinSlider", "generatorLineLengthRandomMaxSlider", "generatorLineLengthValue", "px"],
    ["boxWidth", "generatorBoxWidthSlider", "generatorBoxWidthRandomMinSlider", "generatorBoxWidthRandomMaxSlider", "generatorBoxWidthValue", "px"],
    ["boxHeight", "generatorBoxHeightSlider", "generatorBoxHeightRandomMinSlider", "generatorBoxHeightRandomMaxSlider", "generatorBoxHeightValue", "px"]
  ].map(([key, fixedId, minimumId, maximumId, outputId, suffix]) => ({
    key,
    fixed: byId(fixedId),
    minimum: byId(minimumId),
    maximum: byId(maximumId),
    output: byId(outputId),
    suffix,
    wrapper: document.querySelector(`[data-random-range="${key}"]`)
  }));

  const SEQUENCE_RANGE_CONTROLS = [
    ["speed", "generatorSequenceSpeedMinSlider", "generatorSequenceSpeedSlider", "generatorSequenceSpeedValue", ""],
    ["intensity", "generatorSequenceIntensityMinSlider", "generatorSequenceIntensitySlider", "generatorSequenceIntensityValue", "%"]
  ].map(([key, minimumId, maximumId, outputId, suffix]) => ({
    key,
    minimum: byId(minimumId),
    maximum: byId(maximumId),
    output: byId(outputId),
    suffix,
    alwaysRandom: true,
    wrapper: document.querySelector(`[data-random-range="sequence${key[0].toUpperCase()}${key.slice(1)}"]`)
  }));

  const ALL_RANGE_INPUTS = [
    ...SINGLE_RANGE_OUTPUTS.map((entry) => entry.input),
    ...RANDOM_RANGE_CONTROLS.flatMap((entry) => [entry.fixed, entry.minimum, entry.maximum]),
    ...SEQUENCE_RANGE_CONTROLS.flatMap((entry) => [entry.minimum, entry.maximum])
  ].filter(Boolean);

  const RANDOM_TOGGLE_IDS = {
    gif: "generatorGifRandomToggle",
    modeMix: "generatorModeMixRandomToggle",
    size: "generatorSizeRandomToggle",
    spacing: "generatorSpacingRandomToggle",
    rotation: "generatorRotationRandomToggle",
    opacity: "generatorOpacityRandomToggle",
    tint: "generatorTintRandomToggle",
    spraySpread: "generatorSpraySpreadRandomToggle",
    lineAngle: "generatorLineAngleRandomToggle",
    lineLength: "generatorLineLengthRandomToggle",
    boxWidth: "generatorBoxWidthRandomToggle",
    boxHeight: "generatorBoxHeightRandomToggle",
    boxStyle: "generatorBoxStyleRandomToggle",
    background: "generatorBackgroundRandomToggle"
  };

  const RANDOM_TOGGLES = Object.fromEntries(
    Object.entries(RANDOM_TOGGLE_IDS).map(([key, id]) => [key, byId(id)])
  );

  const GENERATION_RANDOM_TOGGLES = {
    margin: elements.marginRandom,
    marginMode: elements.marginModeRandom,
    count: elements.countRandom,
    sequenceEffects: elements.sequenceEffectsRandom
  };

  const RANGE_RANDOM_TOGGLES = {};

  const state = {
    catalog: [],
    catalogByFolder: new Map(),
    catalogByTag: new Map(),
    catalogBySource: new Map(),
    sourceMode: "category",
    currentWidth: DEFAULT_WIDTH,
    currentHeight: DEFAULT_HEIGHT,
    currentMargin: DEFAULT_MARGIN,
    currentMarginMode: "placement",
    currentCount: 0,
    currentSeed: 0,
    currentSignature: "",
    currentModeCounts: {},
    currentUniqueSourceCount: 0,
    currentSequenceEnabled: false,
    currentSequenceLayerCount: 0,
    currentSequenceEffectCounts: {},
    currentSequenceTimingCounts: {},
    currentSpecs: [],
    currentSettingsUsed: null,
    currentBackground: "#ffffff",
    currentSequenceSummary: null,
    currentBookmarkId: "",
    bookmarks: [],
    bookmarkObjectUrls: [],
    bookmarkDatabasePromise: null,
    bookmarkStorageAvailable: true,
    bookmarkStoragePersisted: null,
    bookmarkSafetyBusy: false,
    activeSessionSaveTimer: null,
    activeSessionSaveRevision: 0,
    activeSessionWritePromise: Promise.resolve(),
    restoringActiveSession: false,
    history: [],
    currentControlState: null,
    dynamicUpdateTimer: null,
    dynamicUpdateBase: null,
    dynamicUpdateAffectsBackground: false,
    dynamicUpdateIncludesNonSequence: false,
    dynamicUpdateSequenceChanges: new Set(),
    applyingHistory: false,
    exportTask: null,
    lastExport: null,
    sequencePaused: false,
    aspectLocked: false,
    lockedAspectRatio: DEFAULT_WIDTH / DEFAULT_HEIGHT,
    generationToken: 0,
    generating: false,
    cropInspectionActive: false,
    pixelatePreviewFrameId: null,
    pixelatePreviewLastUpdate: 0,
    fitFrameId: null,
    loadFailureCount: 0,
    currentFallbackSources: [],
    currentUsedSources: new Set()
  };

  const generatorPixelateProxyMap = new WeakMap();
  const generatorSequenceIterationHandlerMap = new WeakMap();
  let mp4MuxerPromise = null;
  let nextExportRasterSessionId = 1;

  function clamp(value, minimum, maximum) {
    return Math.min(maximum, Math.max(minimum, value));
  }

  function readNumber(input, fallback) {
    const value = Number(input?.value);
    return Number.isFinite(value) ? value : fallback;
  }

  function normalizeInteger(value, fallback, minimum, maximum) {
    const number = Number(value);
    return clamp(Number.isFinite(number) ? Math.round(number) : fallback, minimum, maximum);
  }

  function formatInteger(value) {
    return Math.round(value).toLocaleString();
  }

  function randomSeed() {
    if (globalThis.crypto?.getRandomValues) {
      return globalThis.crypto.getRandomValues(new Uint32Array(1))[0] >>> 0;
    }
    return ((Date.now() ^ Math.floor(Math.random() * 0xffffffff)) >>> 0);
  }

  function parseSeed(value) {
    if (value === null || value === undefined || value === "") {
      return null;
    }
    const raw = String(value).trim();
    const normalized = raw.replace(/^0x/i, "");
    const radix = /^0x/i.test(raw) || /[a-f]/i.test(normalized) ? 16 : 10;
    const parsed = Number.parseInt(normalized, radix);
    return Number.isFinite(parsed) ? parsed >>> 0 : null;
  }

  function formatSeed(seed) {
    return (seed >>> 0).toString(16).padStart(8, "0");
  }

  function createRandom(seed) {
    let value = seed >>> 0;
    return () => {
      value = (value + 0x6d2b79f5) >>> 0;
      let result = value;
      result = Math.imul(result ^ (result >>> 15), result | 1);
      result ^= result + Math.imul(result ^ (result >>> 7), result | 61);
      return ((result ^ (result >>> 14)) >>> 0) / 4294967296;
    };
  }

  function randomBetween(random, minimum, maximum) {
    return minimum + (maximum - minimum) * random();
  }

  function randomInteger(random, minimum, maximum) {
    return Math.floor(randomBetween(random, minimum, maximum + 1));
  }

  function shuffle(values, random) {
    const shuffled = values.slice();
    for (let index = shuffled.length - 1; index > 0; index -= 1) {
      const otherIndex = Math.floor(random() * (index + 1));
      [shuffled[index], shuffled[otherIndex]] = [shuffled[otherIndex], shuffled[index]];
    }
    return shuffled;
  }

  function getConfiguredRange(settings, key) {
    const range = settings?.randomRanges?.[key];
    const fallback = Number(settings?.[key]) || 0;
    const minimum = Number.isFinite(Number(range?.minimum)) ? Number(range.minimum) : fallback;
    const maximum = Number.isFinite(Number(range?.maximum)) ? Number(range.maximum) : fallback;
    return {
      minimum: Math.min(minimum, maximum),
      maximum: Math.max(minimum, maximum)
    };
  }

  function sampleConfiguredRange(settings, key, random, options = {}) {
    const range = getConfiguredRange(settings, key);
    if (
      options.logarithmic &&
      range.minimum > 0 &&
      range.maximum / range.minimum >= 2
    ) {
      return Math.exp(randomBetween(random, Math.log(range.minimum), Math.log(range.maximum)));
    }
    return randomBetween(random, range.minimum, range.maximum);
  }

  function getRepresentativeSetting(settings, key) {
    if (!settings.randomize?.[key]) {
      return Number(settings[key]) || 0;
    }
    const range = getConfiguredRange(settings, key);
    return (range.minimum + range.maximum) / 2;
  }

  function encodeBrushPath(path) {
    return String(path)
      .split("/")
      .map((segment) => encodeURIComponent(segment))
      .join("/");
  }

  function getBrushUrl(source) {
    const url = new URL(`../${encodeBrushPath(source)}`, document.baseURI);
    url.searchParams.set("generatorv", GENERATOR_ASSET_REVISION);
    return url.href;
  }

  function getBrushMetadata(source) {
    const metadata = window.STOCK_BRUSH_METADATA?.[source];
    return metadata && typeof metadata === "object" ? metadata : {};
  }

  function normalizeTags(values) {
    const tags = [];
    const seen = new Set();
    for (const rawTag of Array.isArray(values) ? values : []) {
      const tag = String(rawTag || "").trim().replace(/^#+/, "");
      const key = tag.toLocaleLowerCase();
      if (!tag || seen.has(key)) {
        continue;
      }
      seen.add(key);
      tags.push(tag);
    }
    return tags;
  }

  function buildCatalog() {
    const folders = Array.isArray(window.STOCK_BRUSH_FOLDERS)
      ? window.STOCK_BRUSH_FOLDERS
      : [];
    const seen = new Set();
    const catalog = [];
    const byFolder = new Map();
    const byTag = new Map();

    for (const folder of folders) {
      const folderId = String(folder?.id || "").trim();
      const folderName = String(folder?.name || folderId || "misc").trim();
      const entries = [];
      for (const source of Array.isArray(folder?.files) ? folder.files : []) {
        if (typeof source !== "string" || !/\.gif$/i.test(source) || seen.has(source)) {
          continue;
        }
        seen.add(source);
        const metadata = getBrushMetadata(source);
        const item = {
          source,
          folderId,
          folderName,
          name: String(metadata.name || source.split("/").pop() || "gif"),
          tags: normalizeTags(metadata.tags),
          width: Math.max(1, Number(metadata.width) || 100),
          height: Math.max(1, Number(metadata.height) || 100)
        };
        for (const tag of item.tags) {
          const tagKey = tag.toLocaleLowerCase();
          const taggedEntries = byTag.get(tagKey) || [];
          taggedEntries.push(item);
          byTag.set(tagKey, taggedEntries);
        }
        entries.push(item);
        catalog.push(item);
      }
      if (folderId && entries.length) {
        byFolder.set(folderId, entries);
      }
    }

    state.catalog = catalog;
    state.catalogByFolder = byFolder;
    state.catalogByTag = byTag;
    state.catalogBySource = new Map(catalog.map((item) => [item.source, item]));
    return folders;
  }

  function createSourceChoice(kind, value, labelText, count) {
    const label = document.createElement("label");
    label.className = "generator-source-choice";
    label.title = `${labelText} — ${formatInteger(count)} GIFs`;
    const input = document.createElement("input");
    input.type = "checkbox";
    input.className = "generator-source-checkbox";
    input.checked = true;
    input.dataset.sourceKind = kind;
    input.value = value;
    const name = document.createElement("span");
    name.className = "generator-source-choice-name";
    name.textContent = kind === "tag" ? `#${labelText}` : labelText;
    const countLabel = document.createElement("span");
    countLabel.className = "generator-source-choice-count";
    countLabel.textContent = formatInteger(count);
    label.append(input, name, countLabel);
    return label;
  }

  function populateSourceFilters(folders) {
    const categoryFragment = document.createDocumentFragment();
    for (const folder of folders) {
      const folderId = String(folder?.id || "").trim();
      const entries = state.catalogByFolder.get(folderId);
      if (!entries?.length) {
        continue;
      }
      categoryFragment.appendChild(
        createSourceChoice("category", folderId, String(folder.name || folderId), entries.length)
      );
    }
    elements.categoryList.replaceChildren(categoryFragment);

    const tagFragment = document.createDocumentFragment();
    const tagEntries = Array.from(state.catalogByTag.entries()).sort(([left], [right]) =>
      left.localeCompare(right, undefined, { numeric: true, sensitivity: "base" })
    );
    for (const [tag, entries] of tagEntries) {
      tagFragment.appendChild(createSourceChoice("tag", tag, tag, entries.length));
    }
    elements.tagList.replaceChildren(tagFragment);
  }

  function getSelectedSourceValues(kind) {
    return Array.from(
      document.querySelectorAll(`.generator-source-checkbox[data-source-kind="${kind}"]:checked`)
    ).map((input) => input.value);
  }

  function getActiveCatalog() {
    const kind = state.sourceMode === "tag" ? "tag" : "category";
    const sourceMap = kind === "tag" ? state.catalogByTag : state.catalogByFolder;
    const selectedValues = getSelectedSourceValues(kind);
    const includedSources = new Set();
    const pool = [];
    for (const value of selectedValues) {
      for (const item of sourceMap.get(value) || []) {
        if (includedSources.has(item.source)) {
          continue;
        }
        includedSources.add(item.source);
        pool.push(item);
      }
    }
    return pool;
  }

  function getActiveSourceLabel() {
    const kind = state.sourceMode === "tag" ? "tag" : "category";
    const selected = getSelectedSourceValues(kind);
    const total = document.querySelectorAll(
      `.generator-source-checkbox[data-source-kind="${kind}"]`
    ).length;
    if (selected.length === total && total > 0) {
      return "ALL";
    }
    if (selected.length === 1) {
      if (kind === "tag") {
        return `#${selected[0]}`;
      }
      const folderItem = state.catalogByFolder.get(selected[0])?.[0];
      return folderItem?.folderName || selected[0];
    }
    return `${selected.length} ${kind === "tag" ? "tags" : "categories"}`;
  }

  function setSourceMode(mode, options = {}) {
    const nextMode = mode === "tag" ? "tag" : "category";
    state.sourceMode = nextMode;
    const categoryActive = nextMode === "category";
    elements.categoryTab.setAttribute("aria-selected", String(categoryActive));
    elements.categoryTab.tabIndex = categoryActive ? 0 : -1;
    elements.tagTab.setAttribute("aria-selected", String(!categoryActive));
    elements.tagTab.tabIndex = categoryActive ? -1 : 0;
    elements.categoryPanel.hidden = !categoryActive;
    elements.tagPanel.hidden = categoryActive;
    updateSourceSummary();
    if (options.focus === true) {
      (categoryActive ? elements.categoryTab : elements.tagTab).focus();
    }
  }

  function getSelectedModes() {
    return Array.from(document.querySelectorAll(".generator-mode-checkbox:checked"))
      .map((input) => input.value)
      .filter((mode) => MODE_ORDER.includes(mode));
  }

  function getSelectedSequenceEffects() {
    return Array.from(document.querySelectorAll(".generator-sequence-effect-checkbox:checked"))
      .map((input) => input.value)
      .filter((effect) => SEQUENCE_EFFECTS.includes(effect));
  }

  function getSelectedSequenceTimings() {
    return Array.from(document.querySelectorAll(".generator-sequence-timing-checkbox:checked"))
      .map((input) => input.value)
      .filter((timing) => SEQUENCE_TIMINGS.includes(timing));
  }

  function getCompatibleSequencePairs(effects, timings) {
    const pairs = [];
    for (const effect of effects) {
      for (const timing of timings) {
        if (timing === "grouped" && SEQUENCE_GROUPED_EXCLUSIONS.has(effect)) {
          continue;
        }
        pairs.push({ effect, timing });
      }
    }
    return pairs;
  }

  function hasValidSequenceControls() {
    return !elements.sequenceEnabled.checked || getCompatibleSequencePairs(
      getSelectedSequenceEffects(),
      getSelectedSequenceTimings()
    ).length > 0;
  }

  function updateGenerateAvailability() {
    elements.generate.disabled = state.generating ||
      Boolean(state.exportTask) ||
      getActiveCatalog().length === 0 ||
      !hasValidSequenceControls();
  }

  function updateSequenceControlUI() {
    const enabled = Boolean(elements.sequenceEnabled.checked);
    const effects = getSelectedSequenceEffects();
    const timings = getSelectedSequenceTimings();
    const pairs = getCompatibleSequencePairs(effects, timings);
    elements.sequenceStateLabel.textContent = enabled ? "on" : "off";
    elements.sequenceBody.classList.toggle("is-disabled", !enabled);
    if (!enabled) {
      elements.sequenceHint.textContent = "new compositions will have no added sequence animation";
    } else if (!effects.length) {
      elements.sequenceHint.textContent = "enable at least one sequence effect";
    } else if (!timings.length) {
      elements.sequenceHint.textContent = "enable at least one trigger style";
    } else if (!pairs.length) {
      elements.sequenceHint.textContent = "grouped is unavailable for the selected effects";
    } else {
      elements.sequenceHint.textContent = "one enabled effect and trigger style is chosen per generated layer";
    }
    elements.sequencePause.disabled = !enabled;
    updateGenerateAvailability();
  }

  function setSequencePaused(paused) {
    state.sequencePaused = Boolean(paused);
    elements.canvas.classList.toggle("sequence-paused", state.sequencePaused);
    elements.sequencePause.setAttribute("aria-pressed", String(state.sequencePaused));
    elements.sequencePause.textContent = state.sequencePaused ? "resume preview" : "pause preview";
    scheduleGeneratorPixelatePreview();
    scheduleActiveSessionSave();
  }

  function getCurrentSpecForImage(image) {
    const index = Number(image?.dataset?.generatorIndex);
    return state.currentSpecs.find((spec) => Number(spec.index) === index) || null;
  }

  function applyUncroppedStateToImage(image, spec, paintIndex = 0) {
    const uncropped = Boolean(spec?.uncropped);
    image.classList.toggle("is-generator-uncropped", uncropped);
    image.dataset.generatorUncropped = String(uncropped);
    image.style.setProperty("--generator-uncropped-z", String(1600 + paintIndex));
    if (state.cropInspectionActive) {
      image.setAttribute("aria-pressed", String(uncropped));
    }
  }

  function captureCropInspectionStill(image) {
    if (!(image instanceof HTMLImageElement) || !image.complete || !image.naturalWidth || !image.naturalHeight) {
      return "";
    }
    const scale = Math.min(1, 512 / Math.max(image.naturalWidth, image.naturalHeight));
    const canvas = document.createElement("canvas");
    canvas.width = Math.max(1, Math.round(image.naturalWidth * scale));
    canvas.height = Math.max(1, Math.round(image.naturalHeight * scale));
    const context = canvas.getContext("2d", { alpha: true });
    if (!context) {
      return "";
    }
    context.drawImage(image, 0, 0, canvas.width, canvas.height);
    return canvas.toDataURL("image/png");
  }

  function pauseStampForCropInspection(image) {
    if (
      !(image instanceof HTMLImageElement) ||
      image.dataset.cropInspectionPausedSrc
    ) {
      return;
    }
    if (!image.complete || !image.naturalWidth || !image.naturalHeight) {
      if (image.dataset.cropInspectionPausePending === "true") {
        return;
      }
      image.dataset.cropInspectionPausePending = "true";
      image.addEventListener("load", () => {
        delete image.dataset.cropInspectionPausePending;
        if (state.cropInspectionActive && image.isConnected) {
          pauseStampForCropInspection(image);
        }
      }, { once: true });
      return;
    }
    try {
      const stillSource = captureCropInspectionStill(image);
      if (!stillSource) {
        return;
      }
      image.dataset.cropInspectionPausedSrc = image.getAttribute("src") || image.currentSrc;
      image.src = stillSource;
    } catch (error) {
      // Keep the source visible if this browser cannot snapshot the current frame.
    }
  }

  function resumeStampAfterCropInspection(image) {
    if (!(image instanceof HTMLImageElement)) {
      return;
    }
    delete image.dataset.cropInspectionPausePending;
    const source = image.dataset.cropInspectionPausedSrc;
    if (source) {
      image.src = source;
      delete image.dataset.cropInspectionPausedSrc;
    }
    image.tabIndex = -1;
    image.removeAttribute("role");
    image.removeAttribute("aria-label");
    image.removeAttribute("aria-pressed");
    image.setAttribute("aria-hidden", "true");
  }

  function updateCropInspectionUi() {
    const cropModeSelected = getMarginMode() === "crop";
    const renderedCrop = Boolean(
      state.currentCount &&
      state.currentMarginMode === "crop" &&
      state.currentMargin > 0 &&
      cropModeSelected
    );
    if (!renderedCrop && state.cropInspectionActive) {
      setCropInspectionActive(false);
      return;
    }
    const uncroppedCount = state.currentSpecs.filter((spec) => spec.uncropped).length;
    elements.cropInspect.hidden = !cropModeSelected;
    elements.cropInspect.disabled = !renderedCrop || state.generating || Boolean(state.exportTask);
    elements.cropInspect.setAttribute("aria-pressed", String(state.cropInspectionActive));
    if (!renderedCrop) {
      const configuredMargin = readNumber(elements.margin, 0);
      elements.cropInspect.textContent = configuredMargin > 0
        ? "generate crop to inspect"
        : "set a margin to inspect";
      elements.cropInspectStatus.hidden = false;
      elements.cropInspectStatus.textContent = configuredMargin > 0
        ? "make a new composition to apply this crop"
        : "increase the canvas margin, then make a new composition";
    } else {
      elements.cropInspect.textContent = state.cropInspectionActive
        ? "finish crop inspection"
        : (uncroppedCount ? `edit uncropped gifs (${uncroppedCount})` : "inspect cropped gifs");
      elements.cropInspectStatus.hidden = !state.cropInspectionActive && !uncroppedCount;
      elements.cropInspectStatus.textContent = state.cropInspectionActive
        ? `preview paused · hover to reveal · click to toggle · ${uncroppedCount} uncropped`
        : `${uncroppedCount} ${uncroppedCount === 1 ? "gif remains" : "gifs remain"} uncropped`;
    }
    elements.canvas.dataset.generatorUncroppedCount = String(uncroppedCount);
  }

  function setCropInspectionActive(active) {
    const nextActive = Boolean(active) &&
      state.currentMarginMode === "crop" &&
      state.currentMargin > 0;
    if (state.cropInspectionActive === nextActive) {
      updateCropInspectionUi();
      return;
    }
    state.cropInspectionActive = nextActive;
    elements.canvas.classList.toggle("crop-inspection-active", nextActive);
    for (const image of getSortedLiveStamps()) {
      const spec = getCurrentSpecForImage(image);
      if (nextActive) {
        image.removeAttribute("aria-hidden");
        image.tabIndex = 0;
        image.setAttribute("role", "button");
        image.setAttribute(
          "aria-label",
          `${spec?.uncropped ? "Crop" : "Show"} this GIF beyond the canvas margin`
        );
        image.setAttribute("aria-pressed", String(Boolean(spec?.uncropped)));
        pauseStampForCropInspection(image);
      } else {
        resumeStampAfterCropInspection(image);
      }
    }
    if (!nextActive) {
      scheduleGeneratorPixelatePreview();
    }
    updateCropInspectionUi();
  }

  function toggleStampUncropped(image) {
    if (!state.cropInspectionActive || !(image instanceof HTMLImageElement)) {
      return;
    }
    const spec = getCurrentSpecForImage(image);
    if (!spec) {
      return;
    }
    const historySnapshot = captureGeneratorSnapshot();
    spec.uncropped = !spec.uncropped;
    const paintIndex = Math.max(0, getSortedLiveStamps().indexOf(image));
    applyUncroppedStateToImage(image, spec, paintIndex);
    image.setAttribute(
      "aria-label",
      `${spec.uncropped ? "Crop" : "Show"} this GIF beyond the canvas margin`
    );
    state.currentBookmarkId = "";
    renderBookmarkGallery();
    syncCurrentBookmarkUI();
    updateCropInspectionUi();
    pushHistorySnapshot(historySnapshot);
    scheduleActiveSessionSave();
  }

  function updateRangeOutput(entry) {
    if (!entry.input || !entry.output) {
      return;
    }
    entry.output.textContent = `${formatInteger(readNumber(entry.input, 0))}${entry.suffix}`;
  }

  function readRangeBounds(control) {
    const rawDomainMinimum = Number(control.minimum?.min);
    const rawDomainMaximum = Number(control.minimum?.max);
    const domainMinimum = Number.isFinite(rawDomainMinimum) ? rawDomainMinimum : 0;
    const domainMaximum = Number.isFinite(rawDomainMaximum) ? rawDomainMaximum : domainMinimum;
    const minimum = clamp(readNumber(control.minimum, domainMinimum), domainMinimum, domainMaximum);
    const maximum = clamp(readNumber(control.maximum, domainMaximum), domainMinimum, domainMaximum);
    return {
      minimum: Math.min(minimum, maximum),
      maximum: Math.max(minimum, maximum),
      domainMinimum,
      domainMaximum
    };
  }

  function normalizeRangeControl(control, changedBound = "") {
    if (!control?.minimum || !control.maximum) {
      return { minimum: 0, maximum: 0, domainMinimum: 0, domainMaximum: 0 };
    }
    const rawDomainMinimum = Number(control.minimum.min);
    const rawDomainMaximum = Number(control.minimum.max);
    const domainMinimum = Number.isFinite(rawDomainMinimum) ? rawDomainMinimum : 0;
    const domainMaximum = Number.isFinite(rawDomainMaximum) ? rawDomainMaximum : domainMinimum;
    let minimum = clamp(readNumber(control.minimum, domainMinimum), domainMinimum, domainMaximum);
    let maximum = clamp(readNumber(control.maximum, domainMaximum), domainMinimum, domainMaximum);
    if (minimum > maximum) {
      if (changedBound === "minimum") {
        minimum = maximum;
      } else if (changedBound === "maximum") {
        maximum = minimum;
      } else {
        [minimum, maximum] = [maximum, minimum];
      }
    }
    control.minimum.value = String(minimum);
    control.maximum.value = String(maximum);
    const domainSize = Math.max(1, domainMaximum - domainMinimum);
    const start = (minimum - domainMinimum) / domainSize * 100;
    const size = (maximum - minimum) / domainSize * 100;
    control.wrapper?.style.setProperty("--generator-range-start", `${start}%`);
    control.wrapper?.style.setProperty("--generator-range-size", `${size}%`);
    if (control.wrapper) {
      control.wrapper.dataset.rangeMinimum = String(minimum);
      control.wrapper.dataset.rangeMaximum = String(maximum);
    }
    control.minimum.setAttribute("aria-valuetext", `${formatInteger(minimum)}${control.suffix}`);
    control.maximum.setAttribute("aria-valuetext", `${formatInteger(maximum)}${control.suffix}`);
    return { minimum, maximum, domainMinimum, domainMaximum };
  }

  function updateRandomRangeControl(control, changedBound = "") {
    const bounds = normalizeRangeControl(control, changedBound);
    const randomized = control.alwaysRandom || Boolean(RANDOM_TOGGLES[control.key]?.checked);
    const group = control.wrapper?.closest(".generator-property-group");
    group?.classList.toggle("is-random", randomized);
    if (control.fixed) {
      control.fixed.disabled = randomized;
      control.minimum.disabled = !randomized;
      control.maximum.disabled = !randomized;
    }
    if (!control.output) {
      return bounds;
    }
    control.output.textContent = randomized
      ? `${formatInteger(bounds.minimum)}–${formatInteger(bounds.maximum)}${control.suffix}`
      : `${formatInteger(readNumber(control.fixed, 0))}${control.suffix}`;
    return bounds;
  }

  function getRangeRandomizeKey(control) {
    return control.alwaysRandom
      ? `sequence${control.key[0].toUpperCase()}${control.key.slice(1)}`
      : control.key;
  }

  function formatRangeControlName(key) {
    return String(key)
      .replace(/^sequence/, "sequence ")
      .replace(/([a-z])([A-Z])/g, "$1 $2")
      .toLowerCase();
  }

  function installRangeRandomizationToggles() {
    for (const control of [...RANDOM_RANGE_CONTROLS, ...SEQUENCE_RANGE_CONTROLS]) {
      if (!control.wrapper || control.wrapper.closest(".generator-range-randomize-row")) {
        continue;
      }
      const key = getRangeRandomizeKey(control);
      const name = formatRangeControlName(key);
      const row = document.createElement("div");
      row.className = "generator-range-randomize-row";

      const label = document.createElement("label");
      label.className = "generator-range-randomize-switch";
      label.title = `Randomize the ${name} range with each new composition`;

      const labelText = document.createElement("span");
      labelText.textContent = "range";
      const switchShell = document.createElement("span");
      switchShell.className = "ios-switch";
      const input = document.createElement("input");
      input.id = `generator${key[0].toUpperCase()}${key.slice(1)}RangeRandomToggle`;
      input.className = "generator-range-random-checkbox";
      input.type = "checkbox";
      input.setAttribute("aria-label", `Randomize the ${name} range with new compositions`);
      const slider = document.createElement("span");
      slider.className = "ios-switch-slider";
      slider.setAttribute("aria-hidden", "true");

      switchShell.append(input, slider);
      label.append(labelText, switchShell);
      control.wrapper.before(row);
      row.append(control.wrapper, label);
      RANGE_RANDOM_TOGGLES[key] = input;
    }
  }

  function deriveGenerationControlRandom(seed, key) {
    let mixed = (seed ^ GENERATION_CONTROL_RANDOM_SEED_MASK) >>> 0;
    for (const character of String(key)) {
      mixed ^= character.charCodeAt(0);
      mixed = Math.imul(mixed, 0x01000193) >>> 0;
    }
    return createRandom(mixed);
  }

  function randomizeRangeEndpoints(control, random) {
    const domainMinimum = Number(control.minimum?.min) || 0;
    const domainMaximum = Number(control.minimum?.max) || domainMinimum;
    const step = Math.max(0.0001, Number(control.minimum?.step) || 1);
    const intervalCount = Math.max(0, Math.floor((domainMaximum - domainMinimum) / step));
    let firstIndex = randomInteger(random, 0, intervalCount);
    let secondIndex = randomInteger(random, 0, intervalCount);
    if (firstIndex === secondIndex && intervalCount > 0) {
      secondIndex = firstIndex === intervalCount ? firstIndex - 1 : firstIndex + 1;
    }
    const minimumIndex = Math.min(firstIndex, secondIndex);
    const maximumIndex = Math.max(firstIndex, secondIndex);
    control.minimum.value = String(domainMinimum + minimumIndex * step);
    control.maximum.value = String(domainMinimum + maximumIndex * step);
    updateRandomRangeControl(control);
  }

  function randomizeGeneratedCount(random, minimum, maximum) {
    const upper = Math.max(minimum, maximum);
    const lower = Math.min(upper, Math.max(MIN_RANDOMIZED_COUNT, Math.min(minimum, maximum)));
    const weightedRatio = Math.pow(random(), 2.15);
    return Math.min(upper, lower + Math.floor(weightedRatio * (upper - lower + 1)));
  }

  function randomizeGeneratedMargin(random, maximum) {
    const upper = Math.max(0, Math.floor(maximum));
    if (upper === 0) {
      return 0;
    }

    // Keep the full range reachable, but strongly favor its lower half and give
    // compact margins a dedicated extra chance when the range allows it.
    if (upper >= 64 && random() < 0.2) {
      return randomInteger(random, 0, 63);
    }
    return Math.min(upper, Math.floor(Math.pow(random(), 1.75) * (upper + 1)));
  }

  function randomizeGenerationControls(seed) {
    if (GENERATION_RANDOM_TOGGLES.margin?.checked) {
      const maximum = Math.max(0, Number(elements.margin.max) || 0);
      elements.margin.value = String(randomizeGeneratedMargin(
        deriveGenerationControlRandom(seed, "margin"),
        maximum
      ));
    }
    if (GENERATION_RANDOM_TOGGLES.marginMode?.checked) {
      const random = deriveGenerationControlRandom(seed, "margin-mode");
      const mode = random() < 0.5 ? "placement" : "crop";
      const input = document.querySelector(`input[name="generatorMarginMode"][value="${mode}"]`);
      if (input) {
        input.checked = true;
      }
    }
    if (GENERATION_RANDOM_TOGGLES.count?.checked) {
      elements.count.value = String(randomizeGeneratedCount(
        deriveGenerationControlRandom(seed, "count"),
        Number(elements.count.min) || 1,
        Math.min(Number(elements.count.max) || MAX_GENERATED_COUNT, MAX_GENERATED_COUNT)
      ));
    }
    if (GENERATION_RANDOM_TOGGLES.sequenceEffects?.checked) {
      const random = deriveGenerationControlRandom(seed, "sequence-effects");
      const effectInputs = Array.from(
        document.querySelectorAll(".generator-sequence-effect-checkbox")
      );
      for (const input of effectInputs) {
        input.checked = random() >= 0.5;
      }
      const selectedEffects = getSelectedSequenceEffects();
      const timings = getSelectedSequenceTimings();
      if (!getCompatibleSequencePairs(selectedEffects, timings).length) {
        const compatibleEffects = SEQUENCE_EFFECTS.filter(
          (effect) => getCompatibleSequencePairs([effect], timings).length > 0
        );
        const fallbackEffects = compatibleEffects.length ? compatibleEffects : SEQUENCE_EFFECTS;
        const effect = fallbackEffects[randomInteger(random, 0, fallbackEffects.length - 1)];
        const input = effectInputs.find((candidate) => candidate.value === effect);
        if (input) {
          input.checked = true;
        }
      }
    }
    for (const control of [...RANDOM_RANGE_CONTROLS, ...SEQUENCE_RANGE_CONTROLS]) {
      const key = getRangeRandomizeKey(control);
      if (RANGE_RANDOM_TOGGLES[key]?.checked) {
        randomizeRangeEndpoints(control, deriveGenerationControlRandom(seed, `range-${key}`));
      }
    }
    updateRangeOutputs();
    updateMarginModeUI();
    updateSequenceControlUI();
    updateCropInspectionUi();
  }

  function setRangeHandleFromPointer(control, handle, clientX) {
    const rect = control.wrapper?.getBoundingClientRect();
    if (!rect?.width) {
      return;
    }
    const domainMinimum = Number(handle.min) || 0;
    const domainMaximum = Number(handle.max) || domainMinimum;
    const step = Math.max(0.0001, Number(handle.step) || 1);
    const ratio = clamp((clientX - rect.left) / rect.width, 0, 1);
    const value = Math.round((domainMinimum + ratio * (domainMaximum - domainMinimum)) / step) * step;
    handle.value = String(clamp(value, domainMinimum, domainMaximum));
    handle.dispatchEvent(new Event("input", { bubbles: true }));
  }

  function attachRangePointerInteraction(control) {
    if (!control?.wrapper || !control.minimum || !control.maximum) {
      return;
    }
    control.wrapper.addEventListener("pointerdown", (event) => {
      if (event.button !== undefined && event.button !== 0) {
        return;
      }
      const rect = control.wrapper.getBoundingClientRect();
      const bounds = normalizeRangeControl(control);
      const domainSize = Math.max(1, bounds.domainMaximum - bounds.domainMinimum);
      const targetValue = bounds.domainMinimum + clamp((event.clientX - rect.left) / Math.max(1, rect.width), 0, 1) * domainSize;
      const minimumDistance = Math.abs(targetValue - bounds.minimum);
      const maximumDistance = Math.abs(targetValue - bounds.maximum);
      const handle = minimumDistance === maximumDistance
        ? (targetValue <= (bounds.minimum + bounds.maximum) / 2 ? control.minimum : control.maximum)
        : (minimumDistance < maximumDistance ? control.minimum : control.maximum);
      const changedBound = handle === control.minimum ? "minimum" : "maximum";
      event.preventDefault();
      handle.focus({ preventScroll: true });
      control.wrapper.setPointerCapture?.(event.pointerId);
      const move = (moveEvent) => {
        setRangeHandleFromPointer(control, handle, moveEvent.clientX);
        updateRandomRangeControl(control, changedBound);
      };
      const finish = (finishEvent) => {
        control.wrapper.releasePointerCapture?.(finishEvent.pointerId);
        control.wrapper.removeEventListener("pointermove", move);
        control.wrapper.removeEventListener("pointerup", finish);
        control.wrapper.removeEventListener("pointercancel", finish);
      };
      control.wrapper.addEventListener("pointermove", move);
      control.wrapper.addEventListener("pointerup", finish);
      control.wrapper.addEventListener("pointercancel", finish);
      move(event);
    }, { capture: true });
  }

  function updateRangeOutputs() {
    for (const entry of SINGLE_RANGE_OUTPUTS) {
      updateRangeOutput(entry);
    }
    for (const control of RANDOM_RANGE_CONTROLS) {
      updateRandomRangeControl(control);
    }
    for (const control of SEQUENCE_RANGE_CONTROLS) {
      updateRandomRangeControl(control);
    }
  }

  function updateSourceSummary() {
    const pool = getActiveCatalog();
    elements.catalogCount.textContent = `${formatInteger(pool.length)} gifs`;
    const categorySelected = getSelectedSourceValues("category").length;
    const tagSelected = getSelectedSourceValues("tag").length;
    elements.categorySelectionCount.textContent = `${categorySelected} selected`;
    elements.tagSelectionCount.textContent = `${tagSelected} selected`;

    const maximumCount = pool.length
      ? Math.min(MAX_GENERATED_COUNT, Math.max(MIN_RANDOMIZED_COUNT, pool.length))
      : 0;
    const minimumCount = 1;
    elements.count.min = String(minimumCount);
    elements.count.max = String(Math.max(1, maximumCount));
    const currentCount = readNumber(elements.count, DEFAULT_COUNT);
    if (maximumCount > 0 && currentCount > maximumCount) {
      elements.count.value = String(maximumCount);
    } else if (maximumCount > 0 && currentCount < minimumCount) {
      elements.count.value = String(minimumCount);
    }
    updateRangeOutput(SINGLE_RANGE_OUTPUTS[0]);

    const kind = state.sourceMode === "tag" ? "tag" : "category";
    const selectedCount = kind === "tag" ? tagSelected : categorySelected;
    elements.sourceHint.textContent = selectedCount
      ? `${selectedCount} ${kind === "tag" ? "tags" : "categories"} enabled · matches any selected ${kind}`
      : `select at least one ${kind}`;
    updateGenerateAvailability();
    if (!pool.length && state.currentCount) {
      setStatus(`select at least one ${kind}`, true);
    }
  }

  function markSettingsPending(options = {}) {
    if (!state.currentCount || state.generating) {
      return;
    }
    if (!options.preserveStatus) {
      setStatus("updating composition…");
    }
    requestDynamicCompositionUpdate(options);
    scheduleActiveSessionSave();
  }

  async function commitFutureRandomizationControlChange() {
    if (state.restoringActiveSession || state.applyingHistory) {
      return;
    }
    if (state.dynamicUpdateBase) {
      await applyPendingDynamicUpdate();
      return;
    }
    if (state.currentCount && !state.generating && !state.exportTask) {
      const previousControls = state.currentControlState || captureControlState();
      const historySnapshot = captureGeneratorSnapshot(previousControls);
      state.currentBookmarkId = "";
      state.currentControlState = captureControlState();
      pushHistorySnapshot(historySnapshot);
      renderBookmarkGallery();
      syncCurrentBookmarkUI();
      await flushActiveSessionSave();
      return;
    }
    scheduleActiveSessionSave();
  }

  function setStatus(message, isError = false) {
    elements.status.textContent = message;
    elements.status.classList.toggle("is-error", isError);
  }

  function syncRandomizeAllToggle() {
    const toggles = Object.values(RANDOM_TOGGLES).filter(Boolean);
    const checkedCount = toggles.filter((toggle) => toggle.checked).length;
    elements.randomizeAll.checked = checkedCount === toggles.length;
    elements.randomizeAll.indeterminate = checkedCount > 0 && checkedCount < toggles.length;
    elements.randomizeAll.closest(".ios-switch")?.classList.toggle(
      "is-indeterminate",
      elements.randomizeAll.indeterminate
    );
  }

  function updateAspectLockUI() {
    state.aspectLocked = false;
  }

  function setBookmarkGalleryMode(active, options = {}) {
    const showGallery = Boolean(active);
    elements.controlsMain.hidden = showGallery;
    elements.bookmarksPanel.hidden = !showGallery;
    elements.controls.classList.toggle("is-bookmark-gallery-mode", showGallery);
    elements.bookmarkGalleryMode.setAttribute("aria-pressed", String(showGallery));
    elements.bookmarkGalleryMode.setAttribute(
      "aria-label",
      showGallery ? "Return to generator controls" : "Show bookmarked compositions"
    );
    elements.bookmarkGalleryMode.title = showGallery
      ? "Return to generator controls"
      : "Show bookmarked compositions";
    elements.controls.classList.remove("is-collapsed");
    elements.body.classList.remove("generator-controls-collapsed");
    elements.sidebarToggle.setAttribute("aria-expanded", "true");
    elements.sidebarToggle.setAttribute("aria-label", "Hide generator controls");
    scheduleCanvasFit();
    if (options.focus) {
      (showGallery ? elements.bookmarksPanel : elements.controlsMain).focus({ preventScroll: true });
    }
  }

  function getMarginMode() {
    return document.querySelector('input[name="generatorMarginMode"]:checked')?.value === "crop"
      ? "crop"
      : "placement";
  }

  function normalizeMarginInput(dimensions) {
    const maximum = Math.max(
      0,
      Math.floor(Math.min(dimensions.width, dimensions.height) * MAX_MARGIN_FRACTION)
    );
    const margin = normalizeInteger(elements.margin.value, DEFAULT_MARGIN, 0, maximum);
    elements.margin.max = String(maximum);
    elements.margin.value = String(margin);
    elements.marginValue.textContent = `${formatInteger(margin)}px`;
    return margin;
  }

  function updateMarginModeUI() {
    elements.marginHint.textContent = getMarginMode() === "crop"
      ? "covers the canvas edge above the gif layers"
      : "keeps each gif inside the inset placement area";
  }

  function normalizeDimensionInputs(changedAxis = null) {
    let width = normalizeInteger(elements.width.value, DEFAULT_WIDTH, CANVAS_MIN_SIZE, CANVAS_MAX_SIZE);
    let height = normalizeInteger(elements.height.value, DEFAULT_HEIGHT, CANVAS_MIN_SIZE, CANVAS_MAX_SIZE);
    if (width > 0 && height > 0) {
      state.lockedAspectRatio = width / height;
    }
    elements.width.value = String(width);
    elements.height.value = String(height);
    document.querySelectorAll("[data-canvas-size]").forEach((button) => {
      button.classList.toggle("is-active", button.dataset.canvasSize === `${width}x${height}`);
    });
    normalizeMarginInput({ width, height });
    return { width, height };
  }

  function readSettings() {
    const dimensions = normalizeDimensionInputs();
    const singles = Object.fromEntries(
      SINGLE_RANGE_OUTPUTS.map((entry) => [entry.input.id, readNumber(entry.input, 0)])
    );
    const fixedValues = Object.fromEntries(
      RANDOM_RANGE_CONTROLS.map((control) => [control.key, readNumber(control.fixed, 0)])
    );
    const randomRanges = Object.fromEntries(
      RANDOM_RANGE_CONTROLS.map((control) => {
        const bounds = normalizeRangeControl(control);
        return [control.key, { minimum: bounds.minimum, maximum: bounds.maximum }];
      })
    );
    const sequenceRanges = Object.fromEntries(
      SEQUENCE_RANGE_CONTROLS.map((control) => {
        const bounds = normalizeRangeControl(control);
        return [control.key, { minimum: bounds.minimum, maximum: bounds.maximum }];
      })
    );
    return {
      width: dimensions.width,
      height: dimensions.height,
      margin: singles.generatorMarginSlider,
      marginMode: getMarginMode(),
      count: normalizeInteger(
        elements.count.value,
        DEFAULT_COUNT,
        Number(elements.count.min) || 1,
        Number(elements.count.max) || 500
      ),
      pool: getActiveCatalog(),
      sourceMode: state.sourceMode,
      sourceLabel: getActiveSourceLabel(),
      selectedSources: getSelectedSourceValues(state.sourceMode),
      modes: getSelectedModes(),
      sequence: {
        enabled: Boolean(elements.sequenceEnabled.checked),
        effects: getSelectedSequenceEffects(),
        timings: getSelectedSequenceTimings(),
        speed: sequenceRanges.speed.maximum,
        intensity: sequenceRanges.intensity.maximum,
        ranges: sequenceRanges
      },
      size: fixedValues.size,
      spacing: fixedValues.spacing,
      rotation: fixedValues.rotation,
      opacity: fixedValues.opacity,
      tintAmount: fixedValues.tint,
      tintColor: elements.tintColor.value,
      spraySpread: fixedValues.spraySpread,
      lineAngle: fixedValues.lineAngle,
      lineLength: fixedValues.lineLength,
      boxWidth: fixedValues.boxWidth,
      boxHeight: fixedValues.boxHeight,
      boxStyle: elements.boxStyle.value === "filled" ? "filled" : "outline",
      backgroundColor: elements.backgroundColor.value,
      randomRanges,
      randomize: Object.fromEntries(
        Object.entries(RANDOM_TOGGLES).map(([key, toggle]) => [key, Boolean(toggle?.checked)])
      )
    };
  }

  function chooseBackground(settings, random) {
    if (!settings.randomize.background) {
      return settings.backgroundColor;
    }
    return `#${randomInteger(random, 0, 0xffffff).toString(16).padStart(6, "0")}`;
  }

  function chooseBestAnchor(existingAnchors, width, height, random, marginFactor = 0.08) {
    const marginX = Math.min(width * marginFactor, width / 3);
    const marginY = Math.min(height * marginFactor, height / 3);
    let best = null;
    let bestScore = -Infinity;
    const diagonal = Math.max(1, Math.hypot(width, height));

    for (let attempt = 0; attempt < 14; attempt += 1) {
      const candidate = {
        x: randomBetween(random, marginX, width - marginX),
        y: randomBetween(random, marginY, height - marginY)
      };
      let distanceScore = 0.72;
      if (existingAnchors.length) {
        distanceScore = Math.min(
          ...existingAnchors.map((anchor) => Math.hypot(candidate.x - anchor.x, candidate.y - anchor.y) / diagonal)
        );
      }
      const edgeDistance = Math.min(
        candidate.x / width,
        (width - candidate.x) / width,
        candidate.y / height,
        (height - candidate.y) / height
      );
      const centerDistance = Math.hypot(candidate.x - width / 2, candidate.y - height / 2) / diagonal;
      const score = distanceScore * 1.8 + edgeDistance * 0.18 + centerDistance * 0.09 + random() * 0.08;
      if (score > bestScore) {
        best = candidate;
        bestScore = score;
      }
    }
    return best || { x: width / 2, y: height / 2 };
  }

  function chooseLineAngle(settings, random) {
    if (!settings.randomize.lineAngle) {
      return settings.lineAngle * Math.PI / 180;
    }
    return sampleConfiguredRange(settings, "lineAngle", random) * Math.PI / 180;
  }

  function buildLinePoints(count, settings, random, anchor, motifId) {
    const spacing = settings.randomize.spacing
      ? sampleConfiguredRange(settings, "spacing", random)
      : Math.max(0.1, settings.spacing);
    const lineLimit = settings.randomize.lineLength
      ? sampleConfiguredRange(settings, "lineLength", random)
      : Math.max(0.1, settings.lineLength);
    const angle = chooseLineAngle(settings, random);
    const cos = Math.cos(angle);
    const sin = Math.sin(angle);
    const margin = Math.min(settings.width, settings.height) * 0.025;
    const availableWidth = Math.max(1, settings.width - margin * 2);
    const availableHeight = Math.max(1, settings.height - margin * 2);
    const horizontalLimit = Math.abs(cos) > 0.0001 ? availableWidth / Math.abs(cos) : Infinity;
    const verticalLimit = Math.abs(sin) > 0.0001 ? availableHeight / Math.abs(sin) : Infinity;
    const length = Math.min(
      lineLimit,
      spacing * Math.max(1, count - 1),
      horizontalLimit,
      verticalLimit
    );
    const extentX = Math.abs(cos * length / 2);
    const extentY = Math.abs(sin * length / 2);
    const centerX = clamp(anchor.x, Math.min(settings.width / 2, extentX + margin), Math.max(settings.width / 2, settings.width - extentX - margin));
    const centerY = clamp(anchor.y, Math.min(settings.height / 2, extentY + margin), Math.max(settings.height / 2, settings.height - extentY - margin));
    const bend = randomBetween(random, -0.11, 0.11) * Math.min(length, settings.height);
    const points = [];

    for (let index = 0; index < count; index += 1) {
      const normalized = count === 1 ? 0.5 : index / (count - 1);
      const offset = (normalized - 0.5) * length;
      const curve = Math.sin(normalized * Math.PI) * bend;
      const jitter = count > 3 ? randomBetween(random, -spacing * 0.07, spacing * 0.07) : 0;
      points.push({
        x: clamp(centerX + cos * offset - sin * (curve + jitter), 0, settings.width),
        y: clamp(centerY + sin * offset + cos * (curve + jitter), 0, settings.height),
        mode: "line",
        motifId,
        sampledSpacing: spacing,
        sampledLineLength: lineLimit,
        sampledLineAngle: angle * 180 / Math.PI,
        localScale: randomBetween(random, 0.9, 1.08)
      });
    }
    return points;
  }

  function buildSprayPoints(count, settings, random, anchor, motifId) {
    const spread = settings.randomize.spraySpread
      ? sampleConfiguredRange(settings, "spraySpread", random)
      : Math.max(0.1, settings.spraySpread);
    const ellipse = randomBetween(random, 0.46, 1);
    const angleOffset = randomBetween(random, -Math.PI, Math.PI);
    const points = [];

    for (let index = 0; index < count; index += 1) {
      if (index === 0) {
        points.push({ x: anchor.x, y: anchor.y, mode: "spray", motifId, sampledSpraySpread: spread, localScale: 1.08 });
        continue;
      }
      const theta = random() * Math.PI * 2;
      const radius = Math.sqrt(random()) * spread;
      const localX = Math.cos(theta) * radius;
      const localY = Math.sin(theta) * radius * ellipse;
      const rotatedX = localX * Math.cos(angleOffset) - localY * Math.sin(angleOffset);
      const rotatedY = localX * Math.sin(angleOffset) + localY * Math.cos(angleOffset);
      points.push({
        x: clamp(anchor.x + rotatedX, 0, settings.width),
        y: clamp(anchor.y + rotatedY, 0, settings.height),
        mode: "spray",
        motifId,
        sampledSpraySpread: spread,
        localScale: randomBetween(random, 0.7, 1.15) * (1 - radius / Math.max(1, spread) * 0.16)
      });
    }
    return points;
  }

  function buildBoxOutlinePoints(count, bounds, motifId) {
    const width = bounds.right - bounds.left;
    const height = bounds.bottom - bounds.top;
    const perimeter = Math.max(1, 2 * (width + height));
    const points = [];

    for (let index = 0; index < count; index += 1) {
      let distance = (index / count) * perimeter;
      let x = bounds.left;
      let y = bounds.top;
      if (distance <= width) {
        x += distance;
      } else if ((distance -= width) <= height) {
        x = bounds.right;
        y += distance;
      } else if ((distance -= height) <= width) {
        x = bounds.right - distance;
        y = bounds.bottom;
      } else {
        distance -= width;
        y = bounds.bottom - distance;
      }
      points.push({ x, y, mode: "box", motifId, localScale: 1 });
    }
    return points;
  }

  function buildFilledBoxPoints(count, bounds, motifId, random) {
    const width = bounds.right - bounds.left;
    const height = bounds.bottom - bounds.top;
    const aspect = width / Math.max(1, height);
    const columns = Math.max(1, Math.ceil(Math.sqrt(count * aspect)));
    const rows = Math.max(1, Math.ceil(count / columns));
    const candidates = [];
    for (let row = 0; row < rows; row += 1) {
      for (let column = 0; column < columns; column += 1) {
        candidates.push({
          x: columns === 1 ? (bounds.left + bounds.right) / 2 : bounds.left + column / (columns - 1) * width,
          y: rows === 1 ? (bounds.top + bounds.bottom) / 2 : bounds.top + row / (rows - 1) * height,
          mode: "box",
          motifId,
          localScale: randomBetween(random, 0.92, 1.06)
        });
      }
    }
    return shuffle(candidates, random).slice(0, count);
  }

  function buildBoxPoints(count, settings, random, anchor, motifId) {
    const requestedWidth = settings.randomize.boxWidth
      ? sampleConfiguredRange(settings, "boxWidth", random)
      : settings.boxWidth;
    const requestedHeight = settings.randomize.boxHeight
      ? sampleConfiguredRange(settings, "boxHeight", random)
      : settings.boxHeight;
    const width = clamp(requestedWidth, 1, settings.width);
    const height = clamp(requestedHeight, 1, settings.height);
    const centerX = clamp(anchor.x, width / 2, settings.width - width / 2);
    const centerY = clamp(anchor.y, height / 2, settings.height - height / 2);
    const bounds = {
      left: centerX - width / 2,
      top: centerY - height / 2,
      right: centerX + width / 2,
      bottom: centerY + height / 2
    };
    const style = settings.randomize.boxStyle
      ? (random() < 0.58 ? "outline" : "filled")
      : settings.boxStyle;
    const points = style === "filled"
      ? buildFilledBoxPoints(count, bounds, motifId, random)
      : buildBoxOutlinePoints(count, bounds, motifId);
    for (const point of points) {
      point.sampledBoxWidth = requestedWidth;
      point.sampledBoxHeight = requestedHeight;
      point.sampledBoxStyle = style;
    }
    return points;
  }

  function chooseBestScatterPoint(existingPoints, settings, random) {
    let best = null;
    let bestScore = -Infinity;
    const diagonal = Math.max(1, Math.hypot(settings.width, settings.height));
    for (let attempt = 0; attempt < 10; attempt += 1) {
      const candidate = {
        x: randomBetween(random, 0, settings.width),
        y: randomBetween(random, 0, settings.height)
      };
      const nearestDistance = existingPoints.length
        ? Math.min(...existingPoints.map((point) => Math.hypot(point.x - candidate.x, point.y - candidate.y)))
        : diagonal;
      const score = nearestDistance / diagonal + random() * 0.055;
      if (score > bestScore) {
        best = candidate;
        bestScore = score;
      }
    }
    return best || { x: settings.width / 2, y: settings.height / 2 };
  }

  function buildScatterPoints(count, settings, random, motifId, existingPoints) {
    const points = [];
    for (let index = 0; index < count; index += 1) {
      const point = chooseBestScatterPoint(existingPoints.concat(points), settings, random);
      points.push({
        ...point,
        mode: "scatter",
        motifId,
        localScale: randomBetween(random, 0.72, 1.28)
      });
    }
    return points;
  }

  function getChunkSize(mode, remaining, random, settings) {
    const spacing = Math.max(0.1, getRepresentativeSetting(settings, "spacing"));
    let target;
    if (mode === "line") {
      target = getRepresentativeSetting(settings, "lineLength") / spacing + 1;
    } else if (mode === "spray") {
      target = Math.pow(getRepresentativeSetting(settings, "spraySpread") / spacing, 2) * 1.1;
    } else if (mode === "box") {
      target = 2 * (
        getRepresentativeSetting(settings, "boxWidth") +
        getRepresentativeSetting(settings, "boxHeight")
      ) / spacing;
    } else {
      target = 6;
    }
    const limits = {
      line: [4, 22],
      spray: [6, 24],
      box: [6, 26],
      scatter: [3, 10]
    };
    const [minimum, maximum] = limits[mode] || [2, 8];
    const variedTarget = Math.round(target * randomBetween(random, 0.72, 1.26));
    return Math.min(remaining, clamp(variedTarget, Math.min(minimum, remaining), Math.min(maximum, remaining)));
  }

  function buildCompositionPoints(settings, random) {
    const placementInset = settings.marginMode === "placement" ? settings.margin : 0;
    const geometrySettings = placementInset > 0
      ? {
          ...settings,
          width: Math.max(1, settings.width - placementInset * 2),
          height: Math.max(1, settings.height - placementInset * 2)
        }
      : settings;
    const points = [];
    const anchors = [];
    const modeCounts = Object.fromEntries(settings.modes.map((mode) => [mode, 0]));
    let queue = [];
    let remaining = settings.count;
    let motifId = 0;

    while (remaining > 0) {
      if (!queue.length) {
        queue = settings.randomize.modeMix
          ? shuffle(settings.modes, random)
          : MODE_ORDER.filter((mode) => settings.modes.includes(mode));
      }
      const mode = queue.shift();
      const modesStillDue = queue.length;
      const availableForChunk = Math.max(1, remaining - modesStillDue);
      const chunkSize = getChunkSize(mode, availableForChunk, random, geometrySettings);
      const anchor = chooseBestAnchor(
        anchors,
        geometrySettings.width,
        geometrySettings.height,
        random
      );
      anchors.push(anchor);
      let motifPoints;
      if (mode === "line") {
        motifPoints = buildLinePoints(chunkSize, geometrySettings, random, anchor, motifId);
      } else if (mode === "spray") {
        motifPoints = buildSprayPoints(chunkSize, geometrySettings, random, anchor, motifId);
      } else if (mode === "box") {
        motifPoints = buildBoxPoints(chunkSize, geometrySettings, random, anchor, motifId);
      } else {
        motifPoints = buildScatterPoints(chunkSize, geometrySettings, random, motifId, points);
      }
      points.push(...motifPoints.slice(0, remaining));
      modeCounts[mode] = (modeCounts[mode] || 0) + Math.min(motifPoints.length, remaining);
      remaining -= Math.min(motifPoints.length, remaining);
      motifId += 1;
    }
    const finalPoints = points.slice(0, settings.count);
    if (placementInset > 0) {
      for (const point of finalPoints) {
        point.x += placementInset;
        point.y += placementInset;
      }
    }
    return { points: finalPoints, modeCounts };
  }

  function createBrushBag(pool, random) {
    let available = shuffle(pool, random);
    let index = 0;
    return {
      next() {
        if (!available.length) {
          return null;
        }
        if (index >= available.length) {
          available = shuffle(pool, random);
          index = 0;
        }
        const item = available[index];
        index += 1;
        return item;
      },
      remainingUnused() {
        return available.slice(index);
      }
    };
  }

  function hexToHue(hex) {
    const normalized = String(hex || "").replace("#", "").padEnd(6, "0").slice(0, 6);
    const red = Number.parseInt(normalized.slice(0, 2), 16) / 255;
    const green = Number.parseInt(normalized.slice(2, 4), 16) / 255;
    const blue = Number.parseInt(normalized.slice(4, 6), 16) / 255;
    const maximum = Math.max(red, green, blue);
    const minimum = Math.min(red, green, blue);
    const delta = maximum - minimum;
    if (delta === 0) {
      return 0;
    }
    let hue;
    if (maximum === red) {
      hue = ((green - blue) / delta) % 6;
    } else if (maximum === green) {
      hue = (blue - red) / delta + 2;
    } else {
      hue = (red - green) / delta + 4;
    }
    return ((hue * 60) + 360) % 360;
  }

  function buildVisualSpecs(points, settings, random, preferredSources = []) {
    const brushBag = createBrushBag(settings.pool, random);
    const poolBySource = new Map(settings.pool.map((brush) => [brush.source, brush]));
    const preferredBrushes = preferredSources.map((source) => poolBySource.get(source) || null);
    const fixedBrush = settings.randomize.gif
      ? null
      : (preferredBrushes.find(Boolean) || brushBag.next());
    const usedSources = new Set();
    const nextUnusedBrush = () => {
      for (let attempt = 0; attempt < settings.pool.length; attempt += 1) {
        const candidate = brushBag.next();
        if (candidate && !usedSources.has(candidate.source)) {
          return candidate;
        }
      }
      return brushBag.next();
    };
    const sizeRange = getConfiguredRange(settings, "size");
    const opacityRange = getConfiguredRange(settings, "opacity");
    const tintRange = getConfiguredRange(settings, "tint");
    const specs = points.map((point, index) => {
      const preferredBrush = preferredBrushes[index];
      const brush = settings.randomize.gif
        ? (preferredBrush && !usedSources.has(preferredBrush.source) ? preferredBrush : nextUnusedBrush())
        : fixedBrush;
      if (!brush) {
        return null;
      }
      usedSources.add(brush.source);
      const baseSize = settings.randomize.size
        ? sampleConfiguredRange(settings, "size", random, { logarithmic: true })
        : settings.size;
      const localScale = settings.randomize.size ? (point.localScale || 1) : 1;
      let longestSide = settings.randomize.size
        ? clamp(baseSize * localScale, sizeRange.minimum, sizeRange.maximum)
        : Math.max(0.1, baseSize);
      const sourceRatio = brush.width / Math.max(1, brush.height);
      let width = sourceRatio >= 1 ? longestSide : longestSide * sourceRatio;
      let height = sourceRatio >= 1 ? longestSide / sourceRatio : longestSide;
      const rotation = settings.randomize.rotation
        ? sampleConfiguredRange(settings, "rotation", random)
        : settings.rotation;
      let x = point.x;
      let y = point.y;
      if (settings.marginMode === "placement" && settings.margin > 0) {
        const innerWidth = Math.max(1, settings.width - settings.margin * 2);
        const innerHeight = Math.max(1, settings.height - settings.margin * 2);
        const radians = rotation * Math.PI / 180;
        const absoluteCosine = Math.abs(Math.cos(radians));
        const absoluteSine = Math.abs(Math.sin(radians));
        let halfExtentX = (absoluteCosine * width + absoluteSine * height) / 2;
        let halfExtentY = (absoluteSine * width + absoluteCosine * height) / 2;
        const fitScale = Math.min(
          1,
          innerWidth / Math.max(1, halfExtentX * 2),
          innerHeight / Math.max(1, halfExtentY * 2)
        );
        if (fitScale < 1) {
          width *= fitScale;
          height *= fitScale;
          longestSide *= fitScale;
          halfExtentX *= fitScale;
          halfExtentY *= fitScale;
        }
        x = clamp(
          x,
          settings.margin + halfExtentX,
          settings.width - settings.margin - halfExtentX
        );
        y = clamp(
          y,
          settings.margin + halfExtentY,
          settings.height - settings.margin - halfExtentY
        );
      }
      const opacity = settings.randomize.opacity
        ? randomBetween(random, opacityRange.minimum, opacityRange.maximum) / 100
        : clamp(settings.opacity / 100, 0, 1);
      const tintAmount = settings.randomize.tint
        ? randomBetween(random, tintRange.minimum, tintRange.maximum) / 100
        : clamp(settings.tintAmount / 100, 0, 1);
      const hue = settings.randomize.tint
        ? randomBetween(random, 0, 360)
        : hexToHue(settings.tintColor);
      const filter = tintAmount <= 0.005
        ? ""
        : `sepia(${(tintAmount * 0.72).toFixed(3)}) saturate(${(1 + tintAmount * 3.6).toFixed(3)}) hue-rotate(${(hue - 45).toFixed(1)}deg)`;
      return {
        ...point,
        x,
        y,
        brush,
        index,
        width,
        height,
        rotation,
        opacity,
        tintAmount,
        tintHue: hue,
        filter,
        longestSide
      };
    }).filter(Boolean);

    specs.sort((left, right) => right.longestSide - left.longestSide || left.index - right.index);
    return {
      specs,
      usedSources,
      fallbackSources: brushBag.remainingUnused().filter((brush) => !usedSources.has(brush.source))
    };
  }

  function createSequencePairBag(pairs, random) {
    let available = shuffle(pairs, random);
    let index = 0;
    return () => {
      if (!available.length) {
        return null;
      }
      if (index >= available.length) {
        available = shuffle(pairs, random);
        index = 0;
      }
      const pair = available[index];
      index += 1;
      return pair;
    };
  }

  function getSequenceDelay(timing, index, total, duration, motifPhase, random, reverse) {
    const safeTotal = Math.max(1, total);
    if (timing === "all" || timing === "grouped") {
      return motifPhase;
    }
    if (timing === "random") {
      return motifPhase + random() * duration;
    }
    if (timing === "step") {
      const blockSize = Math.max(1, Math.round(safeTotal * 0.22));
      return motifPhase + Math.floor(index / blockSize) * duration * 0.16;
    }
    const orderedIndex = reverse ? safeTotal - index - 1 : index;
    const spacing = timing === "pulse"
      ? duration / Math.max(4, safeTotal * 1.45)
      : duration * 0.72 / Math.max(1, safeTotal - 1);
    return motifPhase + orderedIndex * spacing;
  }

  function combineSequenceFilter(baseFilter, activeFilter) {
    return baseFilter ? `${baseFilter} ${activeFilter}` : activeFilter;
  }

  function chooseSequenceAlternateBrush(pool, baseSource, random) {
    if (pool.length <= 1) {
      return pool[0] || null;
    }
    let candidate = null;
    for (let attempt = 0; attempt < 8; attempt += 1) {
      candidate = pool[Math.floor(random() * pool.length)] || null;
      if (candidate?.source && candidate.source !== baseSource) {
        return candidate;
      }
    }
    return pool.find((item) => item.source !== baseSource) || null;
  }

  function buildSequenceAssignments(specs, settings, seed, options = {}) {
    const emptySummary = {
      enabled: false,
      layerCount: 0,
      effectCounts: {},
      timingCounts: {}
    };
    const previousSequences = new Map(
      specs
        .filter((spec) => spec.sequence)
        .map((spec) => [Number(spec.index), { ...spec.sequence }])
    );
    for (const spec of specs) {
      spec.sequence = null;
    }
    if (!settings.sequence.enabled) {
      return emptySummary;
    }
    const pairs = getCompatibleSequencePairs(
      settings.sequence.effects,
      settings.sequence.timings
    );
    if (!pairs.length) {
      return emptySummary;
    }

    const random = createRandom((seed ^ SEQUENCE_RANDOM_SEED_MASK) >>> 0);
    const nextPair = createSequencePairBag(pairs, random);
    const preserveExisting = options.preserveExisting === true;
    const changedFields = new Set(options.changedFields || []);
    const specsByMotif = new Map();
    for (const spec of specs) {
      const motifSpecs = specsByMotif.get(spec.motifId) || [];
      motifSpecs.push(spec);
      specsByMotif.set(spec.motifId, motifSpecs);
    }

    const effectCounts = {};
    const timingCounts = {};
    const speedRange = settings.sequence.ranges?.speed || {
      minimum: settings.sequence.speed,
      maximum: settings.sequence.speed
    };
    const intensityRange = settings.sequence.ranges?.intensity || {
      minimum: settings.sequence.intensity,
      maximum: settings.sequence.intensity
    };
    const motifs = Array.from(specsByMotif.entries()).sort(([left], [right]) => left - right);

    for (const [motifId, motifSpecs] of motifs) {
      motifSpecs.sort((left, right) => left.index - right.index);
      const sampledPair = nextPair();
      if (!sampledPair) {
        continue;
      }
      const previousMotifSequence = previousSequences.get(Number(motifSpecs[0]?.index));
      let effect = sampledPair.effect;
      if (
        preserveExisting &&
        previousMotifSequence &&
        !changedFields.has("effects") &&
        settings.sequence.effects.includes(previousMotifSequence.effect) &&
        settings.sequence.timings.some((timing) =>
          timing !== "grouped" || !SEQUENCE_GROUPED_EXCLUSIONS.has(previousMotifSequence.effect)
        )
      ) {
        effect = previousMotifSequence.effect;
      }
      const compatibleTimings = settings.sequence.timings.filter((timing) =>
        timing !== "grouped" || !SEQUENCE_GROUPED_EXCLUSIONS.has(effect)
      );
      if (!compatibleTimings.length) {
        continue;
      }
      let timing = compatibleTimings.includes(sampledPair.timing)
        ? sampledPair.timing
        : compatibleTimings[Math.floor(random() * compatibleTimings.length)];
      if (
        preserveExisting &&
        previousMotifSequence &&
        !changedFields.has("timings") &&
        compatibleTimings.includes(previousMotifSequence.timing)
      ) {
        timing = previousMotifSequence.timing;
      }
      const pair = { effect, timing };
      const sampledSpeed = randomBetween(random, speedRange.minimum, speedRange.maximum);
      const speed = preserveExisting && previousMotifSequence && !changedFields.has("speed")
        ? Number(previousMotifSequence.speed) || sampledSpeed
        : sampledSpeed;
      const duration = Math.round(clamp(6400 - speed * 52, 700, 6200));
      const motifPhase = random() * duration;
      const sampledReverse = random() < 0.5;
      const sampledIntensity = clamp(
        randomBetween(random, intensityRange.minimum, intensityRange.maximum) / 100, 0, 3
      );
      const intensity = preserveExisting && previousMotifSequence && !changedFields.has("intensity")
        ? clamp(Number(previousMotifSequence.intensity) / 100, 0, 3)
        : sampledIntensity;
      const sampledMoveAngle = random() * Math.PI * 2;
      const previousMoveX = Number(previousMotifSequence?.moveX);
      const previousMoveY = Number(previousMotifSequence?.moveY);
      const moveAngle = preserveExisting && Number.isFinite(previousMoveX) && Number.isFinite(previousMoveY)
        ? Math.atan2(previousMoveY, previousMoveX)
        : sampledMoveAngle;
      const moveStrength = Math.max(8, Math.min(settings.width, settings.height) * 0.09 * intensity);
      const moveX = Math.cos(moveAngle) * moveStrength;
      const moveY = Math.sin(moveAngle) * moveStrength;
      const sampledRotationAmount = random() < 0.5 ? -360 : 360;
      const rotationAmount = preserveExisting && Number.isFinite(Number(previousMotifSequence?.rotationAmount))
        ? Number(previousMotifSequence.rotationAmount)
        : sampledRotationAmount;
      const scaleAmount = 1 + 0.18 + intensity * 0.78;
      const sampledHueAmount = Math.round(randomBetween(random, 80, 300) * (random() < 0.5 ? -1 : 1));
      const hueAmount = preserveExisting && Number.isFinite(Number(previousMotifSequence?.hueAmount))
        ? Number(previousMotifSequence.hueAmount)
        : sampledHueAmount;
      const sampledSequenceHue = Math.round((random() * 360 + 360) % 360);
      const sequenceHue = preserveExisting && Number.isFinite(Number(previousMotifSequence?.colorHue))
        ? Number(previousMotifSequence.colorHue)
        : sampledSequenceHue;
      const reverse = preserveExisting && typeof previousMotifSequence?.reverse === "boolean"
        ? previousMotifSequence.reverse
        : sampledReverse;
      const blurAmount = (1.5 + intensity * 11).toFixed(2);
      const pixelateAmount = Math.round(2 + intensity * 14);
      const contrastAmount = (1.25 + intensity * 1.8).toFixed(2);

      effectCounts[pair.effect] = (effectCounts[pair.effect] || 0) + 1;
      timingCounts[pair.timing] = (timingCounts[pair.timing] || 0) + 1;

      motifSpecs.forEach((spec, index) => {
        const previousSequence = previousSequences.get(Number(spec.index));
        let delay;
        if (
          preserveExisting &&
          previousSequence &&
          !changedFields.has("timings")
        ) {
          const previousDuration = Math.max(1, Number(previousSequence.duration) || duration);
          delay = changedFields.has("speed")
            ? Number(previousSequence.delay || 0) * duration / previousDuration
            : Number(previousSequence.delay || 0);
        } else {
          const rawDelay = getSequenceDelay(
            pair.timing,
            index,
            motifSpecs.length,
            duration,
            motifPhase,
            random,
            reverse
          );
          delay = -(rawDelay % duration);
        }
        const baseFilter = spec.filter || "";
        let activeFilter = baseFilter || "none";
        if (pair.effect === "color-cycle") {
          activeFilter = combineSequenceFilter(
            baseFilter,
            `hue-rotate(${hueAmount}deg) saturate(${(1.4 + intensity * 2.8).toFixed(2)})`
          );
        } else if (pair.effect === "blur") {
          activeFilter = combineSequenceFilter(baseFilter, `blur(${blurAmount}px)`);
        } else if (pair.effect === "pixelate") {
          activeFilter = combineSequenceFilter(
            baseFilter,
            `contrast(${contrastAmount}) saturate(${(1 - intensity * 0.38).toFixed(2)})`
          );
        }
        const alternateBrush = pair.effect === "image-cycle"
          ? chooseSequenceAlternateBrush(settings.pool, spec.brush.source, random)
          : null;
        const previousAlternateSource = String(previousSequence?.alternateSource || "");
        const alternateSource = pair.effect === "image-cycle" &&
          preserveExisting &&
          previousAlternateSource &&
          previousAlternateSource !== spec.brush.source &&
          settings.pool.some((brush) => brush.source === previousAlternateSource)
          ? previousAlternateSource
          : (alternateBrush?.source || "");
        spec.sequence = {
          effect: pair.effect,
          timing: pair.timing,
          motifId,
          speed,
          intensity: intensity * 100,
          duration,
          delay,
          reverse,
          moveX,
          moveY,
          rotationAmount,
          scaleAmount,
          filterRest: baseFilter || "none",
          filterActive: activeFilter,
          colorHue: sequenceHue,
          hueAmount,
          activeSaturation: 1.4 + intensity * 2.8,
          blurAmount: Number(blurAmount),
          pixelateAmount,
          contrastAmount: Number(contrastAmount),
          pixelSaturation: 1 - intensity * 0.38,
          alternateSource
        };
      });
    }

    return {
      enabled: true,
      layerCount: motifs.length,
      effectCounts,
      timingCounts
    };
  }

  function buildSignature(specs) {
    return specs.slice(0, 16).map((spec) => [
      spec.brush.source,
      spec.x.toFixed(1),
      spec.y.toFixed(1),
      spec.longestSide.toFixed(1),
      spec.rotation.toFixed(1),
      spec.mode
    ].join("|")).join(";");
  }

  function replaceFailedBrush(image) {
    if (image.dataset.generatorRetry === "1") {
      image.classList.add("is-load-error");
      state.loadFailureCount += 1;
      return;
    }
    let fallback = null;
    while (state.currentFallbackSources.length && !fallback) {
      const candidate = state.currentFallbackSources.shift();
      if (candidate && !state.currentUsedSources.has(candidate.source)) {
        fallback = candidate;
      }
    }
    if (!fallback) {
      image.dataset.generatorRetry = "1";
      state.loadFailureCount += 1;
      return;
    }
    state.currentUsedSources.add(fallback.source);
    image.dataset.generatorRetry = "1";
    image.dataset.generatorSource = fallback.source;
    image.dataset.generatorCategory = fallback.folderId;
    image.src = getBrushUrl(fallback.source);
  }

  function getSequenceCycleUrl(source, image, cycle) {
    const url = new URL(getBrushUrl(source));
    url.hash = `sequence-${image.dataset.generatorMotif || "0"}-${image.dataset.generatorIndex || "0"}-${cycle}`;
    return url.href;
  }

  function getGeneratorPixelateProxy(image) {
    let proxy = generatorPixelateProxyMap.get(image);
    if (proxy?.isConnected) {
      return proxy;
    }
    proxy = document.createElement("canvas");
    proxy.className = "generator-pixelate-proxy";
    proxy.hidden = true;
    proxy.setAttribute("aria-hidden", "true");
    proxy.dataset.generatorIndex = image.dataset.generatorIndex || "";
    generatorPixelateProxyMap.set(image, proxy);
    image.after(proxy);
    return proxy;
  }

  function getGeneratorLiveSequenceProgress(image, sequence) {
    const animation = image.getAnimations().find((candidate) =>
      candidate.animationName === "generator-sequence-pixelate"
    );
    const currentTime = Number(animation?.currentTime);
    if (!Number.isFinite(currentTime)) {
      return null;
    }
    const timing = animation.effect?.getTiming?.() || {};
    const delay = Number.isFinite(Number(timing.delay))
      ? Number(timing.delay)
      : Number(sequence.delay) || 0;
    const duration = Math.max(100, Number(sequence.duration) || 2000);
    return positiveModulo((currentTime - delay) / duration, 1);
  }

  function updateGeneratorPixelatePreview(image) {
    const spec = getCurrentSpecForImage(image);
    const sequence = spec?.sequence;
    if (
      sequence?.effect !== "pixelate" ||
      !image.complete ||
      !image.naturalWidth ||
      !image.naturalHeight
    ) {
      return false;
    }
    const progress = getGeneratorLiveSequenceProgress(image, sequence);
    if (progress === null) {
      return true;
    }
    const pixelate = getGeneratorPixelateState(sequence, progress);
    const proxy = getGeneratorPixelateProxy(image);
    if (pixelate.blockSize <= 1) {
      proxy.hidden = true;
      delete proxy.dataset.generatorPixelateBlockSize;
      image.classList.remove("has-generator-pixelate-proxy");
      return true;
    }

    const width = Math.max(1, Number(spec.width) || image.naturalWidth || 1);
    const height = Math.max(1, Number(spec.height) || image.naturalHeight || 1);
    const renderedWidth = Math.max(1, width * pixelate.scale);
    const renderedHeight = Math.max(1, height * pixelate.scale);
    const pixelWidth = Math.max(1, Math.ceil(renderedWidth / pixelate.blockSize));
    const pixelHeight = Math.max(1, Math.ceil(renderedHeight / pixelate.blockSize));
    if (proxy.width !== pixelWidth) {
      proxy.width = pixelWidth;
    }
    if (proxy.height !== pixelHeight) {
      proxy.height = pixelHeight;
    }
    const context = proxy.getContext("2d", { alpha: true });
    if (!context) {
      return true;
    }
    context.clearRect(0, 0, pixelWidth, pixelHeight);
    context.globalAlpha = 1;
    context.globalCompositeOperation = "source-over";
    context.imageSmoothingEnabled = false;
    try {
      context.drawImage(image, 0, 0, pixelWidth, pixelHeight);
    } catch (error) {
      proxy.hidden = true;
      image.classList.remove("has-generator-pixelate-proxy");
      return true;
    }

    const computed = getComputedStyle(image);
    proxy.style.left = image.style.left;
    proxy.style.top = image.style.top;
    proxy.style.width = image.style.width;
    proxy.style.height = image.style.height;
    proxy.style.opacity = computed.opacity;
    proxy.style.transform = computed.transform;
    proxy.style.filter = computed.filter === "none" ? "" : computed.filter;
    proxy.style.zIndex = computed.zIndex;
    proxy.classList.toggle("is-generator-uncropped", spec.uncropped === true);
    proxy.dataset.generatorPixelateBlockSize = String(pixelate.blockSize);
    proxy.dataset.generatorPixelateScale = pixelate.scale.toFixed(6);
    proxy.hidden = false;
    image.classList.add("has-generator-pixelate-proxy");
    return true;
  }

  function runGeneratorPixelatePreviews(now) {
    state.pixelatePreviewFrameId = null;
    if (state.cropInspectionActive) {
      return;
    }
    if (now - state.pixelatePreviewLastUpdate < PIXELATE_PREVIEW_INTERVAL_MS) {
      scheduleGeneratorPixelatePreview();
      return;
    }
    state.pixelatePreviewLastUpdate = now;
    const images = Array.from(
      elements.composition.querySelectorAll("img.generator-sequence-pixelate")
    );
    let hasPendingPreview = false;
    for (const image of images) {
      hasPendingPreview = updateGeneratorPixelatePreview(image) || hasPendingPreview;
    }
    if (images.length || hasPendingPreview) {
      scheduleGeneratorPixelatePreview();
    }
  }

  function scheduleGeneratorPixelatePreview() {
    if (state.pixelatePreviewFrameId !== null || state.cropInspectionActive) {
      return;
    }
    state.pixelatePreviewFrameId = requestAnimationFrame(runGeneratorPixelatePreviews);
  }

  function clearSequenceSpecFromImage(image, spec, nextSequence = null) {
    const previousEffect = image.dataset.generatorSequenceEffect || "";
    const previousAlternateSource = image.dataset.generatorSequenceAlternateSource || "";
    const preserveImageCycle = previousEffect === "image-cycle" &&
      nextSequence?.effect === "image-cycle" &&
      previousAlternateSource === String(nextSequence.alternateSource || "");
    const preservedCycle = preserveImageCycle
      ? String(image.dataset.generatorSequenceCycle || "0")
      : "0";
    const iterationHandler = generatorSequenceIterationHandlerMap.get(image);
    if (iterationHandler) {
      image.removeEventListener("animationiteration", iterationHandler);
      generatorSequenceIterationHandlerMap.delete(image);
    }
    image.classList.remove("has-generator-sequence", "has-generator-pixelate-proxy");
    for (const effect of SEQUENCE_EFFECTS) {
      image.classList.remove(`generator-sequence-${effect}`);
    }
    for (const timing of SEQUENCE_TIMINGS) {
      image.classList.remove(`generator-sequence-timing-${timing}`);
    }
    for (const property of [
      "--generator-sequence-duration",
      "--generator-sequence-delay",
      "--generator-sequence-move-x",
      "--generator-sequence-move-y",
      "--generator-sequence-rotation",
      "--generator-sequence-scale",
      "--generator-sequence-filter-rest",
      "--generator-sequence-filter-active",
      "--generator-sequence-easing"
    ]) {
      image.style.removeProperty(property);
    }
    for (const key of Object.keys(image.dataset)) {
      if (key.startsWith("generatorSequence")) {
        delete image.dataset[key];
      }
    }
    delete image.dataset.generatorPixelateAmount;
    const pixelateProxy = generatorPixelateProxyMap.get(image);
    if (pixelateProxy) {
      pixelateProxy.remove();
      generatorPixelateProxyMap.delete(image);
    }
    if (previousEffect === "image-cycle" && !preserveImageCycle) {
      const baseSource = getBrushUrl(spec.brush.source);
      if (image.src !== baseSource) {
        image.src = baseSource;
      }
    }
    return preservedCycle;
  }

  function applySequenceSpecToImage(image, spec) {
    const sequence = spec.sequence;
    const preservedCycle = clearSequenceSpecFromImage(image, spec, sequence);
    image.style.setProperty("--generator-base-opacity", String(spec.opacity));
    image.style.setProperty("--generator-base-rotation", `${spec.rotation}deg`);
    if (!sequence) {
      return;
    }
    image.dataset.generatorSequenceEffect = sequence.effect;
    image.dataset.generatorSequenceTiming = sequence.timing;
    image.dataset.generatorSequenceSpeed = Number(sequence.speed || 0).toFixed(3);
    image.dataset.generatorSequenceIntensity = Number(sequence.intensity || 0).toFixed(3);
    if (sequence.effect === "pixelate") {
      image.dataset.generatorPixelateAmount = String(sequence.pixelateAmount || 12);
    }
    image.style.setProperty("--generator-sequence-duration", `${sequence.duration}ms`);
    image.style.setProperty("--generator-sequence-delay", `${sequence.delay}ms`);
    image.style.setProperty("--generator-sequence-move-x", `${sequence.moveX.toFixed(2)}px`);
    image.style.setProperty("--generator-sequence-move-y", `${sequence.moveY.toFixed(2)}px`);
    image.style.setProperty("--generator-sequence-rotation", `${sequence.rotationAmount}deg`);
    image.style.setProperty("--generator-sequence-scale", sequence.scaleAmount.toFixed(3));
    image.style.setProperty("--generator-sequence-filter-rest", sequence.filterRest);
    image.style.setProperty("--generator-sequence-filter-active", sequence.filterActive);
    const easingByTiming = {
      pulse: "cubic-bezier(0.2, 0.72, 0.25, 1)",
      wave: "ease-in-out",
      step: "steps(1, end)",
      random: "steps(2, jump-none)",
      all: "ease-in-out",
      grouped: "ease-in-out"
    };
    image.style.setProperty(
      "--generator-sequence-easing",
      easingByTiming[sequence.timing] || "ease-in-out"
    );

    if (sequence.effect === "image-cycle" && sequence.alternateSource) {
      image.dataset.generatorSequenceBaseSource = spec.brush.source;
      image.dataset.generatorSequenceAlternateSource = sequence.alternateSource;
      image.dataset.generatorSequenceCycle = preservedCycle;
      const iterationHandler = (event) => {
        if (event.animationName !== "generator-sequence-image-cycle") {
          return;
        }
        const cycle = (Number(image.dataset.generatorSequenceCycle) || 0) + 1;
        const source = cycle % 2
          ? image.dataset.generatorSequenceAlternateSource
          : image.dataset.generatorSequenceBaseSource;
        image.dataset.generatorSequenceCycle = String(cycle);
        if (source) {
          image.src = getSequenceCycleUrl(source, image, cycle);
        }
      };
      generatorSequenceIterationHandlerMap.set(image, iterationHandler);
      image.addEventListener("animationiteration", iterationHandler);
    }
    image.classList.add(
      "has-generator-sequence",
      `generator-sequence-${sequence.effect}`,
      `generator-sequence-timing-${sequence.timing}`
    );
  }

  function createStampElement(spec, index) {
    const image = document.createElement("img");
    image.className = "generator-stamp";
    image.alt = "";
    image.setAttribute("aria-hidden", "true");
    image.draggable = false;
    image.loading = index < 36 ? "eager" : "lazy";
    image.decoding = "async";
    image.src = getBrushUrl(spec.brush.source);
    image.style.left = `${spec.x - spec.width / 2}px`;
    image.style.top = `${spec.y - spec.height / 2}px`;
    image.style.width = `${spec.width}px`;
    image.style.height = `${spec.height}px`;
    image.style.opacity = String(spec.opacity);
    image.style.transform = `rotate(${spec.rotation}deg)`;
    image.style.filter = spec.filter;
    image.style.zIndex = String(index + 1);
    image.dataset.generatorMode = spec.mode;
    image.dataset.generatorMotif = String(spec.motifId);
    image.dataset.generatorIndex = String(spec.index);
    image.dataset.generatorSource = spec.brush.source;
    image.dataset.generatorCategory = spec.brush.folderId;
    image.dataset.generatorTags = spec.brush.tags.join(",");
    image.dataset.generatorX = spec.x.toFixed(3);
    image.dataset.generatorY = spec.y.toFixed(3);
    image.dataset.generatorSize = spec.longestSide.toFixed(3);
    image.dataset.generatorRotation = spec.rotation.toFixed(3);
    image.dataset.generatorOpacity = spec.opacity.toFixed(4);
    image.dataset.generatorTintAmount = spec.tintAmount.toFixed(4);
    for (const key of SAMPLED_GEOMETRY_KEYS) {
      if (Number.isFinite(Number(spec[key]))) {
        image.dataset[key] = Number(spec[key]).toFixed(3);
      }
    }
    if (spec.sampledBoxStyle) {
      image.dataset.sampledBoxStyle = spec.sampledBoxStyle;
    }
    applyUncroppedStateToImage(image, spec, index);
    applySequenceSpecToImage(image, spec);
    image.addEventListener("error", () => replaceFailedBrush(image));
    if (spec.sequence?.effect === "pixelate") {
      image.addEventListener("load", scheduleGeneratorPixelatePreview);
    }
    return image;
  }

  function setActionStatus(message, isError = false) {
    elements.actionStatus.textContent = message;
    elements.actionStatus.classList.toggle("is-error", isError);
  }

  function updateBookmarkSafetyUi() {
    const persisted = state.bookmarkStoragePersisted;
    elements.protectBookmarks.disabled = state.bookmarkSafetyBusy || persisted === true;
    elements.protectBookmarks.textContent = persisted === true ? "storage protected" : "protect storage";
    elements.backupBookmarks.disabled = state.bookmarkSafetyBusy || state.bookmarks.length < 1;
    elements.restoreBookmarksButton.disabled = state.bookmarkSafetyBusy;
    elements.restoreBookmarks.disabled = state.bookmarkSafetyBusy;
    elements.bookmarkStorageStatus.classList.toggle("is-protected", persisted === true);
    elements.bookmarkStorageStatus.classList.toggle("is-warning", persisted === false);
    elements.bookmarkStorageStatus.textContent = persisted === true
      ? "browser storage protected · keep a backup for device loss"
      : persisted === false
        ? "browser may clear local data when space is low · keep a backup"
        : "persistent storage unavailable · keep a backup";
  }

  async function requestPersistentBookmarkStorage(options = {}) {
    const storage = navigator.storage;
    if (!storage || typeof storage.persisted !== "function") {
      state.bookmarkStoragePersisted = null;
      updateBookmarkSafetyUi();
      return false;
    }
    try {
      let persisted = await storage.persisted();
      if (!persisted && options.request !== false && typeof storage.persist === "function") {
        persisted = await storage.persist();
      }
      state.bookmarkStoragePersisted = Boolean(persisted);
      updateBookmarkSafetyUi();
      return persisted;
    } catch (error) {
      state.bookmarkStoragePersisted = null;
      updateBookmarkSafetyUi();
      return false;
    }
  }

  function syncCurrentBookmarkUI() {
    const bookmarked = Boolean(state.currentBookmarkId);
    elements.bookmark.classList.toggle("is-bookmarked", bookmarked);
    elements.bookmark.disabled = !state.bookmarkStorageAvailable ||
      !state.currentCount || bookmarked || state.generating || Boolean(state.exportTask);
    elements.bookmark.setAttribute("aria-pressed", String(bookmarked));
    elements.bookmark.querySelector("span:last-child").textContent = bookmarked ? "bookmarked" : "bookmark";
    const exportDisabled = !state.currentCount || state.generating || Boolean(state.exportTask);
    elements.downloadWebp.disabled = exportDisabled;
    elements.downloadMp4.disabled = exportDisabled;
    elements.backgroundOnly.disabled = !state.currentCount || state.generating || Boolean(state.exportTask);
    updateBookmarkSafetyUi();
    updateHistoryUi();
  }

  function openBookmarkDatabase() {
    if (state.bookmarkDatabasePromise) {
      return state.bookmarkDatabasePromise;
    }
    state.bookmarkDatabasePromise = new Promise((resolve, reject) => {
      if (typeof indexedDB === "undefined") {
        reject(new Error("IndexedDB is unavailable"));
        return;
      }
      const request = indexedDB.open(BOOKMARK_DATABASE_NAME, BOOKMARK_DATABASE_VERSION);
      request.onupgradeneeded = () => {
        const database = request.result;
        if (!database.objectStoreNames.contains(BOOKMARK_STORE_NAME)) {
          const store = database.createObjectStore(BOOKMARK_STORE_NAME, { keyPath: "id" });
          store.createIndex("savedAt", "savedAt");
        }
      };
      request.onsuccess = () => {
        state.bookmarkStorageAvailable = true;
        resolve(request.result);
      };
      request.onerror = () => reject(request.error || new Error("Could not open bookmark storage"));
      request.onblocked = () => reject(new Error("Bookmark storage is blocked"));
    }).catch((error) => {
      state.bookmarkDatabasePromise = null;
      throw error;
    });
    return state.bookmarkDatabasePromise;
  }

  async function runBookmarkRequest(mode, operation) {
    const database = await openBookmarkDatabase();
    return new Promise((resolve, reject) => {
      const transaction = database.transaction(BOOKMARK_STORE_NAME, mode);
      const store = transaction.objectStore(BOOKMARK_STORE_NAME);
      let request;
      try {
        request = operation(store);
      } catch (error) {
        reject(error);
        return;
      }
      transaction.oncomplete = () => resolve(request?.result);
      transaction.onerror = () => reject(transaction.error || request?.error || new Error("Bookmark storage failed"));
      transaction.onabort = () => reject(transaction.error || new Error("Bookmark storage was cancelled"));
    });
  }

  function serializeSpec(spec) {
    const serialized = {
      source: spec.brush.source,
      x: spec.x,
      y: spec.y,
      mode: spec.mode,
      motifId: spec.motifId,
      localScale: spec.localScale,
      index: spec.index,
      width: spec.width,
      height: spec.height,
      rotation: spec.rotation,
      opacity: spec.opacity,
      tintAmount: spec.tintAmount,
      tintHue: spec.tintHue,
      filter: spec.filter,
      longestSide: spec.longestSide,
      uncropped: Boolean(spec.uncropped),
      sequence: spec.sequence ? { ...spec.sequence } : null
    };
    for (const key of SAMPLED_GEOMETRY_KEYS) {
      if (Number.isFinite(Number(spec[key]))) {
        serialized[key] = Number(spec[key]);
      }
    }
    if (typeof spec.sampledBoxStyle === "string") {
      serialized.sampledBoxStyle = spec.sampledBoxStyle;
    }
    return serialized;
  }

  function deserializeSpecs(rawSpecs) {
    if (!Array.isArray(rawSpecs) || rawSpecs.length < 1 || rawSpecs.length > 500) {
      throw new Error("This bookmark has an invalid composition");
    }
    return rawSpecs.map((raw, position) => {
      const brush = state.catalogBySource.get(String(raw?.source || ""));
      if (!brush) {
        throw new Error("A bookmarked GIF is no longer in the catalog");
      }
      const width = Math.max(0.1, Number(raw.width) || 0);
      const height = Math.max(0.1, Number(raw.height) || 0);
      if (![raw.x, raw.y, width, height, raw.rotation, raw.opacity].every((value) => Number.isFinite(Number(value)))) {
        throw new Error("This bookmark contains invalid placement data");
      }
      const spec = {
        brush,
        x: Number(raw.x),
        y: Number(raw.y),
        mode: MODE_ORDER.includes(raw.mode) ? raw.mode : "scatter",
        motifId: Math.max(0, Math.floor(Number(raw.motifId)) || 0),
        localScale: Number(raw.localScale) || 1,
        index: Number.isFinite(Number(raw.index)) ? Number(raw.index) : position,
        width,
        height,
        rotation: Number(raw.rotation),
        opacity: clamp(Number(raw.opacity), 0, 1),
        tintAmount: clamp(Number(raw.tintAmount) || 0, 0, 1),
        tintHue: ((Number(raw.tintHue) || 0) % 360 + 360) % 360,
        filter: String(raw.filter || ""),
        longestSide: Math.max(width, height, Number(raw.longestSide) || 0),
        uncropped: Boolean(raw.uncropped),
        sequence: raw.sequence && typeof raw.sequence === "object" ? { ...raw.sequence } : null
      };
      for (const key of SAMPLED_GEOMETRY_KEYS) {
        if (Number.isFinite(Number(raw[key]))) {
          spec[key] = Number(raw[key]);
        }
      }
      if (raw.sampledBoxStyle === "filled" || raw.sampledBoxStyle === "outline") {
        spec.sampledBoxStyle = raw.sampledBoxStyle;
      }
      return spec;
    });
  }

  function captureControlState() {
    return {
      sourceMode: state.sourceMode,
      selectedCategories: getSelectedSourceValues("category"),
      selectedTags: getSelectedSourceValues("tag"),
      width: elements.width.value,
      height: elements.height.value,
      aspectLocked: state.aspectLocked,
      lockedAspectRatio: state.lockedAspectRatio,
      marginMode: getMarginMode(),
      modes: getSelectedModes(),
      ranges: Object.fromEntries(
        ALL_RANGE_INPUTS.map((input) => [input.id, input.value])
      ),
      randomize: Object.fromEntries(
        Object.entries(RANDOM_TOGGLES).map(([key, toggle]) => [key, Boolean(toggle?.checked)])
      ),
      generationRandomize: Object.fromEntries(
        Object.entries(GENERATION_RANDOM_TOGGLES).map(([key, toggle]) => [key, Boolean(toggle?.checked)])
      ),
      rangeRandomize: Object.fromEntries(
        Object.entries(RANGE_RANDOM_TOGGLES).map(([key, toggle]) => [key, Boolean(toggle?.checked)])
      ),
      tintColor: elements.tintColor.value,
      boxStyle: elements.boxStyle.value,
      backgroundColor: elements.backgroundColor.value,
      sequenceEnabled: elements.sequenceEnabled.checked,
      sequenceEffects: getSelectedSequenceEffects(),
      sequenceTimings: getSelectedSequenceTimings(),
      sequencePaused: state.sequencePaused
    };
  }

  function restoreCheckedValues(selector, values) {
    const selected = new Set(Array.isArray(values) ? values.map(String) : []);
    document.querySelectorAll(selector).forEach((input) => {
      input.checked = selected.has(input.value);
    });
  }

  function deriveLegacyRandomRange(key, value) {
    const scalar = Number(value) || 0;
    if (key === "rotation" || key === "lineAngle") {
      return [-180, 180];
    }
    if (key === "opacity") {
      return [Math.max(1, scalar - 48), scalar];
    }
    if (key === "tint") {
      return [0, 66];
    }
    const factors = {
      size: [0.5, 1.72],
      spacing: [0.62, 1.42],
      spraySpread: [0.45, 1.58],
      lineLength: [0.52, 1.52],
      boxWidth: [0.48, 1.48],
      boxHeight: [0.48, 1.48]
    }[key] || [1, 1];
    return [scalar * factors[0], scalar * factors[1]];
  }

  function restoreLegacyRangeEndpoints(controls) {
    const savedRanges = controls?.ranges;
    if (!savedRanges || typeof savedRanges !== "object") {
      return;
    }
    for (const control of RANDOM_RANGE_CONTROLS) {
      const hasMinimum = Object.prototype.hasOwnProperty.call(savedRanges, control.minimum.id);
      const hasMaximum = Object.prototype.hasOwnProperty.call(savedRanges, control.maximum.id);
      if (hasMinimum && hasMaximum) {
        continue;
      }
      const legacyValue = Object.prototype.hasOwnProperty.call(savedRanges, control.fixed.id)
        ? Number(savedRanges[control.fixed.id])
        : readNumber(control.fixed, 0);
      const [minimum, maximum] = deriveLegacyRandomRange(control.key, legacyValue);
      control.minimum.value = String(minimum);
      control.maximum.value = String(maximum);
    }
    for (const control of SEQUENCE_RANGE_CONTROLS) {
      if (Object.prototype.hasOwnProperty.call(savedRanges, control.minimum.id)) {
        continue;
      }
      const legacyValue = Object.prototype.hasOwnProperty.call(savedRanges, control.maximum.id)
        ? Number(savedRanges[control.maximum.id])
        : readNumber(control.maximum, 0);
      if (control.key === "speed") {
        control.minimum.value = String(legacyValue - 13);
        control.maximum.value = String(legacyValue + 13);
      } else {
        control.minimum.value = String(legacyValue * 0.72);
        control.maximum.value = String(legacyValue * 1.2);
      }
    }
  }

  function restoreControlState(controls) {
    if (!controls || typeof controls !== "object") {
      return;
    }
    restoreCheckedValues(
      '.generator-source-checkbox[data-source-kind="category"]',
      controls.selectedCategories
    );
    restoreCheckedValues(
      '.generator-source-checkbox[data-source-kind="tag"]',
      controls.selectedTags
    );
    elements.width.value = String(controls.width || DEFAULT_WIDTH);
    elements.height.value = String(controls.height || DEFAULT_HEIGHT);
    state.aspectLocked = false;
    state.lockedAspectRatio = Number(controls.lockedAspectRatio) || DEFAULT_WIDTH / DEFAULT_HEIGHT;
    const marginMode = controls.marginMode === "crop" ? "crop" : "placement";
    const marginRadio = document.querySelector(`input[name="generatorMarginMode"][value="${marginMode}"]`);
    if (marginRadio) {
      marginRadio.checked = true;
    }
    restoreCheckedValues(".generator-mode-checkbox", controls.modes);
    for (const input of ALL_RANGE_INPUTS) {
      if (controls.ranges && Object.prototype.hasOwnProperty.call(controls.ranges, input.id)) {
        input.value = String(controls.ranges[input.id]);
      }
    }
    restoreLegacyRangeEndpoints(controls);
    for (const [key, toggle] of Object.entries(RANDOM_TOGGLES)) {
      if (toggle && controls.randomize && Object.prototype.hasOwnProperty.call(controls.randomize, key)) {
        toggle.checked = Boolean(controls.randomize[key]);
      }
    }
    for (const [key, toggle] of Object.entries(GENERATION_RANDOM_TOGGLES)) {
      if (toggle) {
        toggle.checked = Boolean(controls.generationRandomize?.[key]);
      }
    }
    for (const [key, toggle] of Object.entries(RANGE_RANDOM_TOGGLES)) {
      if (toggle) {
        toggle.checked = Boolean(controls.rangeRandomize?.[key]);
      }
    }
    elements.tintColor.value = String(controls.tintColor || "#ff4fb3");
    elements.boxStyle.value = controls.boxStyle === "filled" ? "filled" : "outline";
    elements.backgroundColor.value = String(controls.backgroundColor || "#ffffff");
    elements.sequenceEnabled.checked = controls.sequenceEnabled !== false;
    restoreCheckedValues(".generator-sequence-effect-checkbox", controls.sequenceEffects);
    restoreCheckedValues(".generator-sequence-timing-checkbox", controls.sequenceTimings);
    normalizeDimensionInputs();
    updateRangeOutputs();
    updateAspectLockUI();
    updateMarginModeUI();
    syncRandomizeAllToggle();
    updateSequenceControlUI();
    setSourceMode(controls.sourceMode);
    setSequencePaused(Boolean(controls.sequencePaused));
  }

  function createStoredSettings(settings) {
    return {
      width: settings.width,
      height: settings.height,
      margin: settings.margin,
      marginMode: settings.marginMode,
      count: settings.count,
      sourceMode: settings.sourceMode,
      sourceLabel: settings.sourceLabel,
      modes: settings.modes.slice(),
      randomize: { ...settings.randomize },
      randomRanges: Object.fromEntries(
        Object.entries(settings.randomRanges || {}).map(([key, range]) => [key, { ...range }])
      ),
      sequence: {
        enabled: Boolean(settings.sequence?.enabled),
        effects: Array.isArray(settings.sequence?.effects) ? settings.sequence.effects.slice() : [],
        timings: Array.isArray(settings.sequence?.timings) ? settings.sequence.timings.slice() : [],
        ranges: Object.fromEntries(
          Object.entries(settings.sequence?.ranges || {}).map(([key, range]) => [key, { ...range }])
        )
      }
    };
  }

  function captureCurrentComposition() {
    return {
      seed: state.currentSeed,
      background: state.currentBackground,
      settings: { ...state.currentSettingsUsed },
      modeCounts: { ...state.currentModeCounts },
      sequenceSummary: {
        enabled: state.currentSequenceEnabled,
        layerCount: state.currentSequenceLayerCount,
        effectCounts: { ...state.currentSequenceEffectCounts },
        timingCounts: { ...state.currentSequenceTimingCounts }
      },
      specs: state.currentSpecs.map(serializeSpec)
    };
  }

  function cloneStoredValue(value) {
    if (typeof structuredClone === "function") {
      return structuredClone(value);
    }
    return JSON.parse(JSON.stringify(value));
  }

  function captureGeneratorSnapshot(controls = state.currentControlState || captureControlState()) {
    return {
      recordType: "history",
      schemaVersion: BOOKMARK_SCHEMA_VERSION,
      engineRevision: GENERATOR_ASSET_REVISION,
      savedAt: Date.now(),
      currentBookmarkId: state.currentBookmarkId,
      controls: cloneStoredValue(controls),
      composition: captureCurrentComposition()
    };
  }

  function updateHistoryUi() {
    const count = state.history.length;
    elements.undo.hidden = count === 0;
    elements.undo.disabled = count === 0 || state.generating || Boolean(state.exportTask);
    const label = count
      ? `Undo last generator action. ${count} ${count === 1 ? "action" : "actions"} available.`
      : "No generator actions to undo";
    elements.undo.setAttribute("aria-label", label);
    elements.undo.title = count ? `Undo (${count})` : "Nothing to undo";
  }

  function pushHistorySnapshot(snapshot) {
    if (!snapshot?.composition?.specs?.length) {
      return;
    }
    state.history.push(snapshot);
    if (state.history.length > MAX_HISTORY_ACTIONS) {
      state.history.splice(0, state.history.length - MAX_HISTORY_ACTIONS);
    }
    updateHistoryUi();
  }

  async function randomizeActiveBackground() {
    if (!state.currentCount || state.generating || state.exportTask) {
      return false;
    }
    if (state.dynamicUpdateBase) {
      await applyPendingDynamicUpdate();
      if (state.generating || state.exportTask) {
        return false;
      }
    }
    const historySnapshot = captureGeneratorSnapshot();
    let background = state.currentBackground;
    for (let attempt = 0; attempt < 4 && background === state.currentBackground; attempt += 1) {
      background = `#${(randomSeed() & 0xffffff).toString(16).padStart(6, "0")}`;
    }
    state.currentBackground = background;
    state.currentBookmarkId = "";
    elements.canvas.style.backgroundColor = background;
    elements.canvas.style.setProperty("--generator-canvas", background);
    pushHistorySnapshot(historySnapshot);
    renderBookmarkGallery();
    syncCurrentBookmarkUI();
    await flushActiveSessionSave();
    setActionStatus("background randomized");
    return true;
  }

  async function undoLastGeneratorAction() {
    if (state.generating || state.exportTask) {
      return false;
    }
    const pending = takePendingDynamicUpdate();
    const snapshot = pending.snapshot || state.history.pop();
    if (!snapshot) {
      updateHistoryUi();
      return false;
    }
    state.applyingHistory = true;
    try {
      const savedBookmarkId = state.bookmarks.some(
        (bookmark) => bookmark.id === snapshot.currentBookmarkId
      ) ? snapshot.currentBookmarkId : "";
      await restoreCompositionRecord(snapshot, { currentBookmarkId: savedBookmarkId });
      state.applyingHistory = false;
      updateHistoryUi();
      await flushActiveSessionSave();
      setActionStatus("generator action undone");
      return true;
    } catch (error) {
      if (!pending.snapshot) {
        state.history.push(snapshot);
      }
      updateHistoryUi();
      setActionStatus("could not undo that generator action", true);
      return false;
    } finally {
      state.applyingHistory = false;
    }
  }

  function takePendingDynamicUpdate() {
    if (state.dynamicUpdateTimer !== null) {
      clearTimeout(state.dynamicUpdateTimer);
      state.dynamicUpdateTimer = null;
    }
    const pending = {
      snapshot: state.dynamicUpdateBase,
      affectsBackground: state.dynamicUpdateAffectsBackground,
      sequenceOnly: !state.dynamicUpdateIncludesNonSequence &&
        state.dynamicUpdateSequenceChanges.size > 0,
      sequenceChanges: Array.from(state.dynamicUpdateSequenceChanges)
    };
    state.dynamicUpdateBase = null;
    state.dynamicUpdateAffectsBackground = false;
    state.dynamicUpdateIncludesNonSequence = false;
    state.dynamicUpdateSequenceChanges.clear();
    return pending;
  }

  function requestDynamicCompositionUpdate(options = {}) {
    if (state.restoringActiveSession || state.applyingHistory || !state.currentCount) {
      return;
    }
    if (!state.dynamicUpdateBase) {
      state.dynamicUpdateBase = captureGeneratorSnapshot();
    }
    state.dynamicUpdateAffectsBackground ||= Boolean(options.affectsBackground);
    if (typeof options.sequenceChange === "string" && options.sequenceChange) {
      state.dynamicUpdateSequenceChanges.add(options.sequenceChange);
    } else {
      state.dynamicUpdateIncludesNonSequence = true;
    }
    if (state.dynamicUpdateTimer !== null) {
      clearTimeout(state.dynamicUpdateTimer);
    }
    state.dynamicUpdateTimer = setTimeout(() => {
      state.dynamicUpdateTimer = null;
      void applyPendingDynamicUpdate();
    }, DYNAMIC_UPDATE_DELAY_MS);
  }

  async function applySequenceOnlyUpdate(settings, pending) {
    setCropInspectionActive(false);
    const sequenceSummary = buildSequenceAssignments(
      state.currentSpecs,
      settings,
      state.currentSeed,
      {
        preserveExisting: true,
        changedFields: pending.sequenceChanges
      }
    );
    const imagesByIndex = new Map(
      Array.from(elements.composition.querySelectorAll("img.generator-stamp"))
        .map((image) => [Number(image.dataset.generatorIndex), image])
    );
    for (const spec of state.currentSpecs) {
      const image = imagesByIndex.get(Number(spec.index));
      if (image) {
        applySequenceSpecToImage(image, spec);
      }
    }
    state.currentSequenceEnabled = sequenceSummary.enabled;
    state.currentSequenceLayerCount = sequenceSummary.layerCount;
    state.currentSequenceEffectCounts = sequenceSummary.effectCounts;
    state.currentSequenceTimingCounts = sequenceSummary.timingCounts;
    state.currentSequenceSummary = sequenceSummary;
    state.currentSettingsUsed = createStoredSettings(settings);
    state.currentBookmarkId = "";
    state.currentControlState = captureControlState();
    pushHistorySnapshot(pending.snapshot);
    updateCanvasChrome(
      state.currentSettingsUsed,
      state.currentSeed,
      state.currentModeCounts,
      state.currentUniqueSourceCount,
      sequenceSummary
    );
    updateCropInspectionUi();
    scheduleGeneratorPixelatePreview();
    renderBookmarkGallery();
    syncCurrentBookmarkUI();
    await flushActiveSessionSave();
    return true;
  }

  async function applyPendingDynamicUpdate() {
    if (!state.dynamicUpdateBase) {
      return false;
    }
    if (state.generating || state.exportTask) {
      state.dynamicUpdateTimer = setTimeout(() => {
        state.dynamicUpdateTimer = null;
        void applyPendingDynamicUpdate();
      }, DYNAMIC_UPDATE_DELAY_MS);
      return false;
    }
    const settings = readSettings();
    const hasValidSettings = settings.pool.length > 0 &&
      settings.modes.length > 0 &&
      (!settings.sequence.enabled || getCompatibleSequencePairs(
        settings.sequence.effects,
        settings.sequence.timings
      ).length > 0);
    const pending = takePendingDynamicUpdate();
    if (!hasValidSettings) {
      if (!settings.pool.length) {
        setStatus(`select at least one ${settings.sourceMode === "tag" ? "tag" : "category"}`, true);
      } else if (!settings.modes.length) {
        elements.emptyState.hidden = false;
        setStatus("enable at least one placement mode", true);
      } else {
        setStatus("enable a compatible sequence effect and trigger style", true);
      }
      pushHistorySnapshot(pending.snapshot);
      state.currentBookmarkId = "";
      state.currentControlState = captureControlState();
      renderBookmarkGallery();
      syncCurrentBookmarkUI();
      await flushActiveSessionSave();
      return false;
    }
    if (pending.sequenceOnly) {
      return applySequenceOnlyUpdate(settings, pending);
    }
    const preferredSources = state.currentSpecs
      .slice()
      .sort((left, right) => Number(left.index) - Number(right.index))
      .map((spec) => spec.brush.source);
    const uncroppedIndices = state.currentSpecs
      .filter((spec) => spec.uncropped)
      .map((spec) => Number(spec.index));
    return generateComposition({
      seed: state.currentSeed,
      preferredSources,
      uncroppedIndices,
      preserveBackground: !pending.affectsBackground,
      historySnapshot: pending.snapshot,
      dynamic: true
    });
  }

  function createActiveSessionRecord() {
    return {
      id: ACTIVE_SESSION_RECORD_ID,
      recordType: ACTIVE_SESSION_RECORD_TYPE,
      schemaVersion: BOOKMARK_SCHEMA_VERSION,
      engineRevision: GENERATOR_ASSET_REVISION,
      savedAt: Date.now(),
      currentBookmarkId: state.currentBookmarkId,
      controls: captureControlState(),
      composition: captureCurrentComposition(),
      history: state.history.slice(-MAX_HISTORY_ACTIONS).map(cloneStoredValue)
    };
  }

  function enqueueActiveSessionWrite(revision) {
    state.activeSessionWritePromise = state.activeSessionWritePromise
      .catch(() => undefined)
      .then(async () => {
        if (
          revision !== state.activeSessionSaveRevision ||
          state.restoringActiveSession ||
          !state.currentCount ||
          !state.currentSettingsUsed
        ) {
          return false;
        }
        try {
          await runBookmarkRequest("readwrite", (store) => store.put(createActiveSessionRecord()));
          return true;
        } catch (error) {
          return false;
        }
      });
    return state.activeSessionWritePromise;
  }

  function scheduleActiveSessionSave() {
    if (
      state.restoringActiveSession ||
      state.applyingHistory ||
      !state.currentCount ||
      !state.currentSettingsUsed
    ) {
      return;
    }
    if (state.activeSessionSaveTimer !== null) {
      clearTimeout(state.activeSessionSaveTimer);
    }
    const revision = ++state.activeSessionSaveRevision;
    state.activeSessionSaveTimer = setTimeout(() => {
      state.activeSessionSaveTimer = null;
      void enqueueActiveSessionWrite(revision);
    }, ACTIVE_SESSION_SAVE_DELAY_MS);
  }

  function flushActiveSessionSave() {
    if (state.activeSessionSaveTimer !== null) {
      clearTimeout(state.activeSessionSaveTimer);
      state.activeSessionSaveTimer = null;
    }
    if (state.restoringActiveSession || !state.currentCount || !state.currentSettingsUsed) {
      return Promise.resolve(false);
    }
    return enqueueActiveSessionWrite(++state.activeSessionSaveRevision);
  }

  function createBookmarkId() {
    return globalThis.crypto?.randomUUID?.() || `bookmark-${Date.now()}-${Math.random().toString(16).slice(2)}`;
  }

  function readBlobAsDataUrl(blob) {
    if (!(blob instanceof Blob) || !blob.size) {
      return Promise.resolve(null);
    }
    return new Promise((resolve, reject) => {
      const reader = new FileReader();
      reader.onload = () => resolve(typeof reader.result === "string" ? reader.result : null);
      reader.onerror = () => reject(reader.error || new Error("Could not read bookmark preview"));
      reader.readAsDataURL(blob);
    });
  }

  async function decodeBookmarkThumbnail(dataUrl) {
    if (typeof dataUrl !== "string" || !/^data:image\/(?:png|webp|jpeg);base64,/i.test(dataUrl)) {
      return null;
    }
    if (dataUrl.length > Math.ceil(BOOKMARK_THUMBNAIL_MAX_BYTES * 1.4)) {
      return null;
    }
    const response = await fetch(dataUrl);
    const blob = await response.blob();
    return blob.size > 0 && blob.size <= BOOKMARK_THUMBNAIL_MAX_BYTES ? blob : null;
  }

  async function createBookmarkBackupBlob() {
    const bookmarks = [];
    for (const record of state.bookmarks) {
      const thumbnailDataUrl = await readBlobAsDataUrl(record.thumbnailBlob);
      const { thumbnailBlob, ...serializableRecord } = record;
      bookmarks.push({ ...serializableRecord, thumbnailDataUrl });
    }
    const payload = {
      format: BOOKMARK_BACKUP_FORMAT,
      version: BOOKMARK_BACKUP_VERSION,
      exportedAt: Date.now(),
      bookmarkCount: bookmarks.length,
      bookmarks
    };
    return new Blob([JSON.stringify(payload)], { type: "application/json" });
  }

  async function backupBookmarksToFile() {
    if (state.bookmarkSafetyBusy || !state.bookmarks.length) {
      return false;
    }
    state.bookmarkSafetyBusy = true;
    updateBookmarkSafetyUi();
    setActionStatus("preparing bookmark backup…");
    try {
      const blob = await createBookmarkBackupBlob();
      const date = new Date().toISOString().slice(0, 10);
      downloadGeneratorBlob(blob, `image-draw-bookmarks-${date}.json`);
      setActionStatus(`${formatInteger(state.bookmarks.length)} bookmarks backed up`);
      return true;
    } catch (error) {
      setActionStatus("could not create bookmark backup", true);
      return false;
    } finally {
      state.bookmarkSafetyBusy = false;
      updateBookmarkSafetyUi();
    }
  }

  async function normalizeBookmarkBackupRecord(rawRecord) {
    if (
      !rawRecord ||
      rawRecord.schemaVersion !== BOOKMARK_SCHEMA_VERSION ||
      typeof rawRecord.id !== "string" ||
      !rawRecord.id ||
      !Number.isFinite(Number(rawRecord.savedAt)) ||
      !rawRecord.controls ||
      !rawRecord.composition ||
      !Array.isArray(rawRecord.composition.specs)
    ) {
      throw new Error("This backup contains an invalid bookmark");
    }
    deserializeSpecs(rawRecord.composition.specs);
    const settings = rawRecord.composition.settings;
    if (!settings || !Number.isFinite(Number(settings.width)) || !Number.isFinite(Number(settings.height))) {
      throw new Error("This backup contains invalid composition settings");
    }
    const thumbnailBlob = await decodeBookmarkThumbnail(rawRecord.thumbnailDataUrl);
    const record = {
      id: rawRecord.id,
      schemaVersion: BOOKMARK_SCHEMA_VERSION,
      engineRevision: String(rawRecord.engineRevision || GENERATOR_ASSET_REVISION),
      savedAt: Number(rawRecord.savedAt),
      thumbnailBlob,
      controls: rawRecord.controls,
      composition: rawRecord.composition
    };
    return record;
  }

  async function restoreBookmarksFromFile(file) {
    if (state.bookmarkSafetyBusy || !(file instanceof File)) {
      return false;
    }
    if (!file.size || file.size > BOOKMARK_BACKUP_MAX_BYTES) {
      setActionStatus("this bookmark backup is empty or too large", true);
      return false;
    }
    state.bookmarkSafetyBusy = true;
    updateBookmarkSafetyUi();
    setActionStatus("checking bookmark backup…");
    try {
      const payload = JSON.parse(await file.text());
      if (
        payload?.format !== BOOKMARK_BACKUP_FORMAT ||
        payload?.version !== BOOKMARK_BACKUP_VERSION ||
        !Array.isArray(payload.bookmarks)
      ) {
        throw new Error("This is not a compatible bookmark backup");
      }
      if (!payload.bookmarks.length || payload.bookmarks.length > MAX_BOOKMARKS) {
        throw new Error("This backup has an invalid number of bookmarks");
      }
      const restored = [];
      for (const rawRecord of payload.bookmarks) {
        restored.push(await normalizeBookmarkBackupRecord(rawRecord));
      }
      const merged = new Map(state.bookmarks.map((record) => [record.id, record]));
      for (const record of restored) {
        merged.set(record.id, record);
      }
      if (merged.size > MAX_BOOKMARKS) {
        throw new Error(`Restoring this backup would exceed the ${MAX_BOOKMARKS} bookmark limit`);
      }
      await runBookmarkRequest("readwrite", (store) => {
        for (const record of merged.values()) {
          store.put(record);
        }
      });
      await refreshBookmarks();
      syncCurrentBookmarkUI();
      await flushActiveSessionSave();
      setActionStatus(`${formatInteger(restored.length)} bookmarks restored from backup`);
      return true;
    } catch (error) {
      setActionStatus(error.message || "could not restore bookmark backup", true);
      return false;
    } finally {
      state.bookmarkSafetyBusy = false;
      updateBookmarkSafetyUi();
    }
  }

  function formatBookmarkDate(savedAt) {
    try {
      return new Intl.DateTimeFormat(undefined, {
        month: "short",
        day: "numeric",
        hour: "numeric",
        minute: "2-digit"
      }).format(new Date(savedAt));
    } catch (error) {
      return "saved composition";
    }
  }

  function revokeBookmarkObjectUrls() {
    for (const url of state.bookmarkObjectUrls) {
      URL.revokeObjectURL(url);
    }
    state.bookmarkObjectUrls = [];
  }

  function renderBookmarkGallery() {
    revokeBookmarkObjectUrls();
    elements.bookmarkGallery.replaceChildren();
    elements.bookmarkCount.textContent = String(state.bookmarks.length);
    elements.bookmarkEmpty.hidden = state.bookmarks.length > 0;
    const fragment = document.createDocumentFragment();
    for (const record of state.bookmarks) {
      const card = document.createElement("article");
      card.className = "generator-bookmark-card";
      card.classList.toggle("is-current", record.id === state.currentBookmarkId);
      const loadButton = document.createElement("button");
      loadButton.type = "button";
      loadButton.className = "generator-bookmark-load";
      const dateText = formatBookmarkDate(record.savedAt);
      loadButton.setAttribute("aria-label", `Load composition saved ${dateText}`);
      if (record.id === state.currentBookmarkId) {
        loadButton.setAttribute("aria-current", "true");
      }
      if (record.thumbnailBlob instanceof Blob) {
        const image = document.createElement("img");
        const objectUrl = URL.createObjectURL(record.thumbnailBlob);
        state.bookmarkObjectUrls.push(objectUrl);
        image.className = "generator-bookmark-preview";
        image.src = objectUrl;
        image.alt = "";
        loadButton.appendChild(image);
      } else {
        const placeholder = document.createElement("span");
        placeholder.className = "generator-bookmark-preview generator-bookmark-preview-placeholder";
        placeholder.textContent = "preview unavailable";
        loadButton.appendChild(placeholder);
      }
      const meta = document.createElement("span");
      meta.className = "generator-bookmark-meta";
      const title = document.createElement("strong");
      title.textContent = `${formatInteger(record.composition?.specs?.length || 0)} gifs · ${record.composition?.settings?.sourceLabel || "ALL"}`;
      const date = document.createElement("small");
      date.textContent = dateText;
      meta.append(title, date);
      loadButton.appendChild(meta);
      loadButton.addEventListener("click", () => void loadBookmark(record));

      const deleteButton = document.createElement("button");
      deleteButton.type = "button";
      deleteButton.className = "generator-bookmark-delete";
      deleteButton.textContent = "×";
      deleteButton.setAttribute("aria-label", `Delete composition saved ${dateText}`);
      deleteButton.addEventListener("click", () => void deleteBookmark(record));
      card.append(loadButton, deleteButton);
      fragment.appendChild(card);
    }
    elements.bookmarkGallery.appendChild(fragment);
  }

  async function refreshBookmarks() {
    try {
      const records = await runBookmarkRequest("readonly", (store) => store.getAll());
      state.bookmarks = (Array.isArray(records) ? records : [])
        .filter((record) =>
          record?.schemaVersion === BOOKMARK_SCHEMA_VERSION &&
          record?.recordType !== ACTIVE_SESSION_RECORD_TYPE &&
          record?.id !== ACTIVE_SESSION_RECORD_ID
        )
        .sort((left, right) => Number(right.savedAt) - Number(left.savedAt));
      renderBookmarkGallery();
      updateBookmarkSafetyUi();
    } catch (error) {
      state.bookmarkStorageAvailable = false;
      elements.bookmark.disabled = true;
      setActionStatus("bookmark storage is unavailable in this browser", true);
    }
  }

  async function bookmarkCurrentComposition() {
    if (!state.currentCount || state.currentBookmarkId || state.generating || state.exportTask) {
      return;
    }
    if (state.bookmarks.length >= MAX_BOOKMARKS) {
      setActionStatus("bookmark limit reached — delete one before saving another", true);
      return;
    }
    await requestPersistentBookmarkStorage();
    setCropInspectionActive(false);
    const token = state.generationToken;
    elements.bookmark.disabled = true;
    setActionStatus("saving composition…");
    let thumbnailBlob = null;
    try {
      thumbnailBlob = await createCompositionThumbnailBlob();
    } catch (error) {
      thumbnailBlob = null;
    }
    if (token !== state.generationToken) {
      setActionStatus("composition changed before it could be bookmarked", true);
      syncCurrentBookmarkUI();
      return;
    }
    const id = createBookmarkId();
    const record = {
      id,
      schemaVersion: BOOKMARK_SCHEMA_VERSION,
      engineRevision: GENERATOR_ASSET_REVISION,
      savedAt: Date.now(),
      thumbnailBlob,
      controls: captureControlState(),
      composition: captureCurrentComposition()
    };
    try {
      await runBookmarkRequest("readwrite", (store) => store.put(record));
      state.currentBookmarkId = id;
      await refreshBookmarks();
      await flushActiveSessionSave();
      setActionStatus("composition bookmarked locally");
    } catch (error) {
      setActionStatus("could not save bookmark — browser storage may be full", true);
    }
    syncCurrentBookmarkUI();
  }

  async function restoreCompositionRecord(record, options = {}) {
    setCropInspectionActive(false);
    const specs = deserializeSpecs(record?.composition?.specs);
    const settings = record?.composition?.settings;
    if (!settings || !Number.isFinite(Number(settings.width)) || !Number.isFinite(Number(settings.height))) {
      throw new Error("This saved composition has invalid settings");
    }
    restoreControlState(record.controls);
    state.generationToken += 1;
    elements.emptyState.hidden = true;
    const fragment = document.createDocumentFragment();
    specs.forEach((spec, index) => fragment.appendChild(createStampElement(spec, index)));
    elements.composition.replaceChildren(fragment, elements.marginOverlay);
    const background = String(record.composition.background || "#ffffff");
    state.currentWidth = Number(settings.width);
    state.currentHeight = Number(settings.height);
    state.currentMargin = Number(settings.margin) || 0;
    state.currentMarginMode = settings.marginMode === "crop" ? "crop" : "placement";
    state.currentCount = specs.length;
    state.currentSeed = Number(record.composition.seed) >>> 0;
    state.currentSpecs = specs;
    state.currentSettingsUsed = { ...settings, count: specs.length };
    state.currentBackground = background;
    state.currentModeCounts = { ...(record.composition.modeCounts || {}) };
    state.currentUniqueSourceCount = new Set(specs.map((spec) => spec.brush.source)).size;
    const sequenceSummary = record.composition.sequenceSummary || {};
    state.currentSequenceEnabled = Boolean(sequenceSummary.enabled);
    state.currentSequenceLayerCount = Number(sequenceSummary.layerCount) || 0;
    state.currentSequenceEffectCounts = { ...(sequenceSummary.effectCounts || {}) };
    state.currentSequenceTimingCounts = { ...(sequenceSummary.timingCounts || {}) };
    state.currentSequenceSummary = {
      enabled: state.currentSequenceEnabled,
      layerCount: state.currentSequenceLayerCount,
      effectCounts: state.currentSequenceEffectCounts,
      timingCounts: state.currentSequenceTimingCounts
    };
    state.currentSignature = buildSignature(specs);
    state.currentBookmarkId = String(options.currentBookmarkId || "");
    state.currentFallbackSources = getActiveCatalog().filter(
      (item) => !specs.some((spec) => spec.brush.source === item.source)
    );
    state.currentUsedSources = new Set(specs.map((spec) => spec.brush.source));
    state.loadFailureCount = 0;
    elements.composition.style.width = `${state.currentWidth}px`;
    elements.composition.style.height = `${state.currentHeight}px`;
    applyMarginPresentation({ margin: state.currentMargin, marginMode: state.currentMarginMode });
    elements.canvas.style.backgroundColor = background;
    elements.canvas.style.setProperty("--generator-canvas", background);
    updateCanvasChrome(
      state.currentSettingsUsed,
      state.currentSeed,
      state.currentModeCounts,
      state.currentUniqueSourceCount,
      state.currentSequenceSummary
    );
    setSequencePaused(Boolean(record.controls?.sequencePaused));
    state.currentControlState = captureControlState();
    updateCropInspectionUi();
    scheduleCanvasFit();
    renderBookmarkGallery();
    syncCurrentBookmarkUI();
  }

  async function loadBookmark(record) {
    if (state.generating || state.exportTask) {
      return;
    }
    const pending = takePendingDynamicUpdate();
    const historySnapshot = pending.snapshot || captureGeneratorSnapshot();
    try {
      await restoreCompositionRecord(record, { currentBookmarkId: record.id });
      pushHistorySnapshot(historySnapshot);
      await flushActiveSessionSave();
      setActionStatus("bookmarked composition loaded");
    } catch (error) {
      setActionStatus(error.message || "could not load this bookmark", true);
    }
  }

  async function restoreActiveSession() {
    try {
      const record = await runBookmarkRequest(
        "readonly",
        (store) => store.get(ACTIVE_SESSION_RECORD_ID)
      );
      if (
        !record ||
        record.recordType !== ACTIVE_SESSION_RECORD_TYPE ||
        record.schemaVersion !== BOOKMARK_SCHEMA_VERSION
      ) {
        return false;
      }
      state.restoringActiveSession = true;
      const savedBookmarkId = state.bookmarks.some((bookmark) => bookmark.id === record.currentBookmarkId)
        ? record.currentBookmarkId
        : "";
      await restoreCompositionRecord(record, { currentBookmarkId: savedBookmarkId });
      state.history = (Array.isArray(record.history) ? record.history : [])
        .filter((snapshot) =>
          snapshot?.schemaVersion === BOOKMARK_SCHEMA_VERSION &&
          Array.isArray(snapshot?.composition?.specs) &&
          snapshot.composition.specs.length > 0 &&
          snapshot.composition.specs.length <= 500
        )
        .slice(-MAX_HISTORY_ACTIONS);
      updateHistoryUi();
      return true;
    } catch (error) {
      try {
        await runBookmarkRequest("readwrite", (store) => store.delete(ACTIVE_SESSION_RECORD_ID));
      } catch (deleteError) {
        // A corrupt draft should never prevent a fresh composition from loading.
      }
      return false;
    } finally {
      state.restoringActiveSession = false;
    }
  }

  async function deleteBookmark(record) {
    if (!record?.id || !globalThis.confirm("Delete this bookmarked composition?")) {
      return;
    }
    try {
      await runBookmarkRequest("readwrite", (store) => store.delete(record.id));
      if (state.currentBookmarkId === record.id) {
        state.currentBookmarkId = "";
      }
      await refreshBookmarks();
      syncCurrentBookmarkUI();
      await flushActiveSessionSave();
      setActionStatus("bookmark deleted");
    } catch (error) {
      setActionStatus("could not delete bookmark", true);
    }
  }

  function getSortedLiveStamps() {
    return Array.from(elements.composition.querySelectorAll(".generator-stamp"))
      .sort((left, right) => (Number(left.style.zIndex) || 0) - (Number(right.style.zIndex) || 0));
  }

  function drawLiveStamp(context, image, scaleX, scaleY) {
    if (!(image instanceof HTMLImageElement) || !image.complete || !image.naturalWidth) {
      return false;
    }
    const width = Number.parseFloat(image.style.width) || 0;
    const height = Number.parseFloat(image.style.height) || 0;
    const left = Number.parseFloat(image.style.left) || 0;
    const top = Number.parseFloat(image.style.top) || 0;
    if (!(width > 0 && height > 0)) {
      return false;
    }
    const computed = getComputedStyle(image);
    const transform = computed.transform && computed.transform !== "none"
      ? new DOMMatrix(computed.transform)
      : new DOMMatrix();
    context.save();
    context.globalAlpha = clamp(Number(computed.opacity) || 0, 0, 1);
    if ("filter" in context) {
      context.filter = computed.filter === "none" ? "none" : computed.filter;
    }
    context.translate((left + width / 2) * scaleX, (top + height / 2) * scaleY);
    context.transform(
      transform.a,
      transform.b,
      transform.c,
      transform.d,
      transform.e * scaleX,
      transform.f * scaleY
    );
    context.drawImage(image, -width * scaleX / 2, -height * scaleY / 2, width * scaleX, height * scaleY);
    context.restore();
    return true;
  }

  function paintCropMargin(context, outputWidth, outputHeight, scaleX, scaleY) {
    if (state.currentMarginMode !== "crop" || state.currentMargin <= 0) {
      return;
    }
    const marginX = Math.min(outputWidth / 2, state.currentMargin * scaleX);
    const marginY = Math.min(outputHeight / 2, state.currentMargin * scaleY);
    context.save();
    context.fillStyle = state.currentBackground;
    context.fillRect(0, 0, outputWidth, marginY);
    context.fillRect(0, outputHeight - marginY, outputWidth, marginY);
    context.fillRect(0, marginY, marginX, outputHeight - marginY * 2);
    context.fillRect(outputWidth - marginX, marginY, marginX, outputHeight - marginY * 2);
    context.restore();
  }

  function renderLiveCompositionCanvas(outputWidth, outputHeight) {
    const canvas = document.createElement("canvas");
    canvas.width = Math.max(1, Math.round(outputWidth));
    canvas.height = Math.max(1, Math.round(outputHeight));
    const context = canvas.getContext("2d", { alpha: false });
    if (!context) {
      throw new Error("Could not create composition preview");
    }
    context.fillStyle = state.currentBackground;
    context.fillRect(0, 0, canvas.width, canvas.height);
    const scaleX = canvas.width / Math.max(1, state.currentWidth);
    const scaleY = canvas.height / Math.max(1, state.currentHeight);
    const images = getSortedLiveStamps();
    const uncroppedImages = state.currentMarginMode === "crop"
      ? images.filter((image) => image.dataset.generatorUncropped === "true")
      : [];
    const regularImages = uncroppedImages.length
      ? images.filter((image) => image.dataset.generatorUncropped !== "true")
      : images;
    for (const image of regularImages) {
      drawLiveStamp(context, image, scaleX, scaleY);
    }
    paintCropMargin(context, canvas.width, canvas.height, scaleX, scaleY);
    for (const image of uncroppedImages) {
      drawLiveStamp(context, image, scaleX, scaleY);
    }
    return canvas;
  }

  function canvasToBlob(canvas, type, quality) {
    return new Promise((resolve, reject) => {
      canvas.toBlob(
        (blob) => blob ? resolve(blob) : reject(new Error("Could not encode composition preview")),
        type,
        quality
      );
    });
  }

  async function createCompositionThumbnailBlob() {
    const images = getSortedLiveStamps();
    await Promise.race([
      Promise.all(images.map((image) => {
        if (image.complete && image.naturalWidth > 0) {
          return image.decode?.().catch(() => {}) || Promise.resolve();
        }
        return new Promise((resolve) => {
          const finish = () => {
            image.removeEventListener("load", finish);
            image.removeEventListener("error", finish);
            resolve();
          };
          image.addEventListener("load", finish, { once: true });
          image.addEventListener("error", finish, { once: true });
        });
      })),
      new Promise((resolve) => window.setTimeout(resolve, 1800))
    ]);
    const scale = Math.min(
      300 / Math.max(1, state.currentWidth),
      200 / Math.max(1, state.currentHeight)
    );
    const width = Math.max(1, Math.round(state.currentWidth * scale));
    const height = Math.max(1, Math.round(state.currentHeight * scale));
    const canvas = renderLiveCompositionCanvas(width, height);
    try {
      return await canvasToBlob(canvas, "image/webp", 0.8);
    } catch (error) {
      return canvasToBlob(canvas, "image/png");
    }
  }

  function createExportCancellationError() {
    const error = new Error("Composition export cancelled");
    error.name = "AbortError";
    return error;
  }

  function throwIfExportCancelled(task) {
    if (task?.cancelled) {
      throw createExportCancellationError();
    }
  }

  function updateGeneratorExportProgress(task, percent, label) {
    if (!task || state.exportTask !== task) {
      return;
    }
    const progress = clamp(Math.round(Number(percent) || 0), 0, 100);
    elements.exportProgress.hidden = false;
    elements.exportProgress.setAttribute("aria-valuenow", String(progress));
    elements.exportProgress.setAttribute("aria-valuetext", `${label} ${progress}%`);
    elements.exportProgressBar.style.width = `${progress}%`;
    setActionStatus(`${label.toLowerCase()} ${progress}%`);
  }

  function setGeneratorExportUi(active, task = null) {
    elements.exportCancel.hidden = !active;
    elements.exportCancel.disabled = !active;
    elements.exportProgress.hidden = !active;
    if (!active) {
      elements.exportProgress.setAttribute("aria-valuenow", "0");
      elements.exportProgress.removeAttribute("aria-valuetext");
      elements.exportProgressBar.style.width = "0%";
    } else if (task) {
      elements.exportProgress.setAttribute(
        "aria-label",
        task.format === "mp4" ? "MP4 export progress" : "Animated WebP export progress"
      );
      updateGeneratorExportProgress(task, 0, "Preparing");
    }
    updateGenerateAvailability();
    syncCurrentBookmarkUI();
    updateCropInspectionUi();
  }

  function createGeneratorExportTask(format) {
    const task = {
      format,
      cancelled: false,
      rasterSession: null,
      videoEncoder: null,
      cancel() {
        if (this.cancelled) {
          return;
        }
        this.cancelled = true;
        this.rasterSession?.cancel();
        try {
          this.videoEncoder?.close();
        } catch (error) {
          // The encoder may already have finished or entered a closed state.
        }
        this.videoEncoder = null;
      }
    };
    return task;
  }

  function cancelGeneratorExport() {
    if (!state.exportTask) {
      return false;
    }
    state.exportTask.cancel();
    elements.exportCancel.disabled = true;
    setActionStatus("cancelling export…");
    return true;
  }

  function createGeneratorRasterSession(task, onProgress) {
    if (typeof Worker !== "function" || typeof window.OffscreenCanvas !== "function") {
      throw new Error("This browser cannot render an animated WebP safely");
    }
    const worker = new Worker(EXPORT_RASTER_WORKER_URL, { type: "module" });
    const jobId = `generator-export-${nextExportRasterSessionId++}`;
    const pending = new Map();
    let nextRequestId = 1;
    let closed = false;
    let readySettled = false;
    let resolveReady;
    let rejectReady;
    const ready = new Promise((resolve, reject) => {
      resolveReady = resolve;
      rejectReady = reject;
    });
    const startupTimer = window.setTimeout(() => {
      if (!readySettled) {
        readySettled = true;
        rejectReady(new Error("The animation renderer took too long to start"));
      }
    }, EXPORT_STARTUP_TIMEOUT_MS);

    const close = (error = null) => {
      if (closed) {
        return;
      }
      closed = true;
      window.clearTimeout(startupTimer);
      try {
        worker.terminate();
      } catch (terminationError) {
        // A crashed worker may already be gone.
      }
      const reason = error || createExportCancellationError();
      for (const request of pending.values()) {
        window.clearTimeout(request.timer);
        request.reject(reason);
      }
      pending.clear();
      if (!readySettled) {
        readySettled = true;
        rejectReady(reason);
      }
    };

    const request = (type, payload, timeoutMs) => new Promise((resolve, reject) => {
      if (closed || task.cancelled) {
        reject(createExportCancellationError());
        return;
      }
      const requestId = `${jobId}-${nextRequestId++}`;
      const timer = window.setTimeout(() => {
        pending.delete(requestId);
        reject(new Error(`The animation renderer timed out during ${type}`));
      }, timeoutMs);
      pending.set(requestId, { resolve, reject, timer, type });
      try {
        worker.postMessage({
          protocol: EXPORT_RASTER_PROTOCOL,
          version: EXPORT_RASTER_VERSION,
          type,
          requestId,
          jobId,
          ...payload
        });
      } catch (error) {
        window.clearTimeout(timer);
        pending.delete(requestId);
        reject(error);
      }
    });

    worker.addEventListener("message", (event) => {
      const message = event.data || {};
      if (message.protocol !== EXPORT_RASTER_PROTOCOL || message.version !== EXPORT_RASTER_VERSION) {
        return;
      }
      if (message.type === "ready" && message.action === "startup") {
        if (!readySettled) {
          readySettled = true;
          window.clearTimeout(startupTimer);
          resolveReady(message);
        }
        return;
      }
      if (message.type === "error" && message.action === "startup") {
        const error = new Error(message.error?.message || "The animation renderer could not start");
        error.code = message.error?.code || "EXPORT_STARTUP_FAILED";
        close(error);
        return;
      }
      if (message.type === "progress") {
        onProgress?.(message);
        return;
      }
      const activeRequest = pending.get(message.requestId);
      if (!activeRequest) {
        return;
      }
      pending.delete(message.requestId);
      window.clearTimeout(activeRequest.timer);
      if (message.type === "error") {
        const error = new Error(message.error?.message || "The animation renderer failed");
        error.code = message.error?.code || "EXPORT_RASTER_FAILED";
        error.details = message.error?.details || null;
        if (message.error?.cancelled || task.cancelled) {
          error.name = "AbortError";
        }
        activeRequest.reject(error);
      } else {
        activeRequest.resolve(message);
      }
    });
    worker.addEventListener("error", (event) => {
      close(new Error(event.message || "The animation renderer crashed"));
    });
    worker.addEventListener("messageerror", () => {
      close(new Error("The animation renderer returned unreadable data"));
    });

    const session = {
      async prepare(scene) {
        await ready;
        throwIfExportCancelled(task);
        return request("prepare", { scene }, EXPORT_PREPARE_TIMEOUT_MS);
      },
      async renderFrame(timeMs, entries) {
        const message = await request(
          "render-frame",
          { output: "rgba", timeMs, entries },
          EXPORT_FRAME_TIMEOUT_MS
        );
        return message.output;
      },
      cancel() {
        if (!closed) {
          try {
            worker.postMessage({
              protocol: EXPORT_RASTER_PROTOCOL,
              version: EXPORT_RASTER_VERSION,
              type: "cancel",
              jobId
            });
          } catch (error) {
            // Termination below is authoritative.
          }
        }
        close(createExportCancellationError());
      },
      release() {
        if (!closed) {
          try {
            worker.postMessage({
              protocol: EXPORT_RASTER_PROTOCOL,
              version: EXPORT_RASTER_VERSION,
              type: "release",
              jobId
            });
          } catch (error) {
            // Termination below still releases all worker-owned resources.
          }
        }
        close(createExportCancellationError());
      }
    };
    task.rasterSession = session;
    return session;
  }

  function positiveModulo(value, divisor) {
    if (!(divisor > 0)) {
      return 0;
    }
    return ((value % divisor) + divisor) % divisor;
  }

  function smoothStep(value) {
    const normalized = clamp(value, 0, 1);
    return normalized * normalized * (3 - 2 * normalized);
  }

  function sampleCubicBezierCoordinate(value, firstControl, secondControl) {
    const inverse = 1 - value;
    return 3 * inverse * inverse * value * firstControl +
      3 * inverse * value * value * secondControl +
      value * value * value;
  }

  function solveCubicBezierProgress(progress, x1, y1, x2, y2) {
    const target = clamp(progress, 0, 1);
    let lower = 0;
    let upper = 1;
    let parameter = target;
    for (let iteration = 0; iteration < 10; iteration += 1) {
      const sampledX = sampleCubicBezierCoordinate(parameter, x1, x2);
      if (sampledX < target) {
        lower = parameter;
      } else {
        upper = parameter;
      }
      parameter = (lower + upper) / 2;
    }
    return sampleCubicBezierCoordinate(parameter, y1, y2);
  }

  function hslToHex(hue, saturation = 82, lightness = 54) {
    const h = positiveModulo(Number(hue) || 0, 360) / 360;
    const s = clamp(Number(saturation) || 0, 0, 100) / 100;
    const l = clamp(Number(lightness) || 0, 0, 100) / 100;
    const hueToRgb = (p, q, rawT) => {
      const t = positiveModulo(rawT, 1);
      if (t < 1 / 6) return p + (q - p) * 6 * t;
      if (t < 1 / 2) return q;
      if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
      return p;
    };
    let red = l;
    let green = l;
    let blue = l;
    if (s > 0) {
      const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
      const p = 2 * l - q;
      red = hueToRgb(p, q, h + 1 / 3);
      green = hueToRgb(p, q, h);
      blue = hueToRgb(p, q, h - 1 / 3);
    }
    return `#${[red, green, blue]
      .map((channel) => Math.round(channel * 255).toString(16).padStart(2, "0"))
      .join("")}`;
  }

  function getExportRasterBudgetBytes() {
    const memory = Number(navigator.deviceMemory);
    if (Number.isFinite(memory) && memory >= 8) {
      return 512 * 1024 * 1024;
    }
    if (Number.isFinite(memory) && memory > 0 && memory <= 2) {
      return 256 * 1024 * 1024;
    }
    return 384 * 1024 * 1024;
  }

  function getMetadataDuration(source) {
    const metadata = getBrushMetadata(source);
    if (metadata.animated === false || Number(metadata.frameCount) <= 1) {
      return 0;
    }
    const duration = Number(metadata.durationMs);
    return Number.isFinite(duration) && duration >= 40 ? duration : 0;
  }

  function getSequenceLoopKey(sequence) {
    return sequence
      ? `${sequence.motifId}|${sequence.effect}|${Math.round(Number(sequence.duration) || 0)}`
      : "";
  }

  function getExactLoopRate(periodMs, loopDurationMs, minimumRate, maximumRate) {
    const period = Number(periodMs);
    const duration = Number(loopDurationMs);
    if (!(period > 0 && duration > 0)) {
      return { rate: 1, seam: 0, adjusted: false };
    }
    const approximateCycles = duration / period;
    const center = Math.max(1, Math.round(approximateCycles));
    let best = null;
    for (let cycles = Math.max(1, center - 2); cycles <= center + 2; cycles += 1) {
      const rate = cycles * period / duration;
      if (rate < minimumRate || rate > maximumRate) {
        continue;
      }
      const penalty = Math.abs(Math.log(rate));
      if (!best || penalty < best.penalty) {
        best = { rate, seam: 0, adjusted: Math.abs(rate - 1) > 0.0001, penalty };
      }
    }
    if (best) {
      return best;
    }
    const nearestCycles = Math.max(1, Math.round(approximateCycles));
    return {
      rate: 1,
      seam: Math.abs(approximateCycles - nearestCycles),
      adjusted: false,
      penalty: 0
    };
  }

  function collectExportAnimationWeights(specs, durationOverrides = null) {
    const sources = new Map();
    const sequences = new Map();
    const addSource = (source, weight) => {
      if (!source) {
        return;
      }
      const override = durationOverrides?.get(source);
      const duration = Number(override) || getMetadataDuration(source);
      if (!(duration > 0)) {
        return;
      }
      const current = sources.get(source) || { duration, weight: 0 };
      current.duration = duration;
      current.weight += weight;
      sources.set(source, current);
    };
    for (const spec of specs) {
      const visualWeight = Math.max(1, spec.width * spec.height * clamp(spec.opacity, 0.08, 1));
      addSource(spec.brush.source, visualWeight);
      if (spec.sequence?.effect === "image-cycle" && spec.sequence.alternateSource) {
        addSource(spec.sequence.alternateSource, visualWeight * 0.72);
      }
      if (spec.sequence) {
        const key = getSequenceLoopKey(spec.sequence);
        if (!sequences.has(key)) {
          const period = Math.max(100, Number(spec.sequence.duration) || 2000) *
            (spec.sequence.effect === "image-cycle" ? 2 : 1);
          sequences.set(key, { period, weight: Math.sqrt(visualWeight) });
        }
      }
    }
    return { sources, sequences };
  }

  function createGeneratorLoopPlan(specs, durationOverrides = null, forcedDurationMs = null) {
    const animations = collectExportAnimationWeights(specs, durationOverrides);
    const sourceWeightTotal = Array.from(animations.sources.values())
      .reduce((sum, item) => sum + item.weight, 0) || 1;
    const sequenceWeightTotal = Array.from(animations.sequences.values())
      .reduce((sum, item) => sum + item.weight, 0) || 1;
    const candidates = forcedDurationMs
      ? [clamp(Math.round(forcedDurationMs / 10) * 10, EXPORT_LOOP_MIN_MS, EXPORT_LOOP_MAX_MS)]
      : Array.from(
          { length: Math.floor((EXPORT_LOOP_MAX_MS - EXPORT_LOOP_MIN_MS) / 100) + 1 },
          (_, index) => EXPORT_LOOP_MIN_MS + index * 100
        );
    let bestDuration = candidates[0];
    let bestScore = Infinity;
    for (const duration of candidates) {
      let score = 0;
      for (const item of animations.sources.values()) {
        const match = getExactLoopRate(item.duration, duration, 0.67, 1.5);
        score += (item.weight / sourceWeightTotal) *
          (match.seam * 1.8 + Math.abs(Math.log(match.rate)) * 0.13);
      }
      for (const item of animations.sequences.values()) {
        const match = getExactLoopRate(item.period, duration, 0.72, 1.38);
        score += (item.weight / sequenceWeightTotal) *
          (match.seam * 0.55 + Math.abs(Math.log(match.rate)) * 0.045);
      }
      score += ((duration - EXPORT_LOOP_MIN_MS) /
        Math.max(1, EXPORT_LOOP_MAX_MS - EXPORT_LOOP_MIN_MS)) * 0.025;
      if (score < bestScore) {
        bestScore = score;
        bestDuration = duration;
      }
    }
    const sourceRates = new Map();
    for (const [source, item] of animations.sources) {
      sourceRates.set(source, getExactLoopRate(item.duration, bestDuration, 0.67, 1.5).rate);
    }
    const sequenceRates = new Map();
    for (const [key, item] of animations.sequences) {
      sequenceRates.set(key, getExactLoopRate(item.period, bestDuration, 0.72, 1.38).rate);
    }
    return {
      durationMs: bestDuration,
      sourceRates,
      sequenceRates,
      score: bestScore
    };
  }

  function getGeneratorExportFrameInterval(specs, loopPlan) {
    let fastestBlurCycleMs = Number.POSITIVE_INFINITY;
    for (const spec of specs) {
      const sequence = spec.sequence;
      if (sequence?.effect !== "blur") {
        continue;
      }
      const sequenceRate = loopPlan?.sequenceRates?.get(getSequenceLoopKey(sequence)) || 1;
      fastestBlurCycleMs = Math.min(
        fastestBlurCycleMs,
        Math.max(100, Number(sequence.duration) || 2000) / Math.max(0.01, sequenceRate)
      );
    }
    if (!Number.isFinite(fastestBlurCycleMs)) {
      return EXPORT_FRAME_INTERVAL_MS;
    }
    const targetInterval = Math.round(
      fastestBlurCycleMs / EXPORT_BLUR_TARGET_SAMPLES_PER_CYCLE / 10
    ) * 10;
    return clamp(targetInterval, EXPORT_BLUR_MIN_FRAME_INTERVAL_MS, EXPORT_FRAME_INTERVAL_MS);
  }

  function getGeneratorExportDimensions() {
    return {
      width: Math.max(1, state.currentWidth),
      height: Math.max(1, state.currentHeight),
      scale: 1
    };
  }

  function createGeneratorFrameDelays(
    loopDurationMs,
    frameIntervalMs = EXPORT_FRAME_INTERVAL_MS
  ) {
    const durationUnits = Math.max(2, Math.round(loopDurationMs / 10));
    const desiredFrames = Math.max(
      2,
      Math.round(loopDurationMs / frameIntervalMs)
    );
    const frameCount = Math.min(durationUnits, desiredFrames);
    const baseUnits = Math.floor(durationUnits / frameCount);
    let remainder = durationUnits - baseUnits * frameCount;
    return Array.from({ length: frameCount }, () => {
      const units = baseUnits + (remainder > 0 ? 1 : 0);
      remainder = Math.max(0, remainder - 1);
      return Math.max(10, units * 10);
    });
  }

  function getSequenceTriangleLevel(sequence, progress) {
    if (sequence.timing === "step") {
      return progress >= 0.5 ? 1 : 0;
    }
    if (sequence.timing === "random") {
      return progress >= 0.25 && progress < 0.75 ? 1 : 0;
    }
    const descending = progress > 0.5;
    const segmentProgress = descending ? (progress - 0.5) * 2 : progress * 2;
    const easedProgress = sequence.timing === "pulse"
      ? solveCubicBezierProgress(segmentProgress, 0.2, 0.72, 0.25, 1)
      : solveCubicBezierProgress(segmentProgress, 0.42, 0, 0.58, 1);
    return clamp(descending ? 1 - easedProgress : easedProgress, 0, 1);
  }

  function getGeneratorPixelateState(sequence, progress) {
    // This is the canonical pixel grid for both the live canvas proxy and the
    // exported raster frame. Keeping the rounding here prevents the preview
    // and download from drifting by a pixel at intermediate animation phases.
    const level = getSequenceTriangleLevel(sequence, progress);
    const baseAmount = clamp(
      Math.round(Number(sequence?.pixelateAmount) || 12),
      1,
      64
    );
    return {
      blockSize: level > 0 ? Math.max(1, Math.round(baseAmount * level)) : 0,
      level,
      scale: 1 - 0.06 * level
    };
  }

  function interpolateSequenceKeyframes(progress, points) {
    for (let index = 1; index < points.length; index += 1) {
      const left = points[index - 1];
      const right = points[index];
      if (progress <= right[0]) {
        const segment = Math.max(0.0001, right[0] - left[0]);
        const amount = smoothStep((progress - left[0]) / segment);
        return left[1] + (right[1] - left[1]) * amount;
      }
    }
    return points[points.length - 1][1];
  }

  function createGeneratorExportEntry(spec, timeMs, loopPlan) {
    const sequence = spec.sequence;
    let centerX = spec.x;
    let centerY = spec.y;
    let width = spec.width;
    let height = spec.height;
    let rotation = spec.rotation;
    let opacity = spec.opacity;
    let source = spec.brush.source;
    let pixelateAmount = 0;
    let blurAmount = 0;
    const tintLayers = [];
    if (spec.tintAmount > 0.005) {
      tintLayers.push({
        color: hslToHex(spec.tintHue, 84, 54),
        amountPercent: clamp(spec.tintAmount * 58, 0, 72)
      });
    }

    if (sequence) {
      const duration = Math.max(100, Number(sequence.duration) || 2000);
      const sequenceRate = loopPlan.sequenceRates.get(getSequenceLoopKey(sequence)) || 1;
      const position = (timeMs * sequenceRate - (Number(sequence.delay) || 0)) / duration;
      const progress = positiveModulo(position, 1);
      const level = getSequenceTriangleLevel(sequence, progress);
      if (sequence.effect === "show-hide") {
        opacity *= interpolateSequenceKeyframes(progress, [
          [0, 1], [0.32, 1], [0.46, 0], [0.54, 0], [0.68, 1], [1, 1]
        ]);
      } else if (sequence.effect === "move") {
        centerX += (Number(sequence.moveX) || 0) * level;
        centerY += (Number(sequence.moveY) || 0) * level;
      } else if (sequence.effect === "rotate") {
        rotation += (Number(sequence.rotationAmount) || 360) * progress;
      } else if (sequence.effect === "scale") {
        const scale = 1 + (Math.max(1, Number(sequence.scaleAmount) || 1) - 1) * level;
        width *= scale;
        height *= scale;
      } else if (sequence.effect === "color-cycle") {
        tintLayers.push({
          color: hslToHex(sequence.colorHue, 88, 55),
          amountPercent: clamp((Number(sequence.colorAmount) || 54) * level, 0, 72)
        });
      } else if (sequence.effect === "image-cycle" && sequence.alternateSource) {
        const initialIteration = Math.floor((-(Number(sequence.delay) || 0)) / duration);
        const currentIteration = Math.floor(position);
        if (positiveModulo(currentIteration - initialIteration, 2) === 1) {
          source = sequence.alternateSource;
        }
        opacity *= interpolateSequenceKeyframes(progress, [
          [0, 1], [0.38, 1], [0.49, 0.24], [0.51, 0.24], [0.62, 1], [1, 1]
        ]);
      } else if (sequence.effect === "pixelate") {
        const pixelate = getGeneratorPixelateState(sequence, progress);
        pixelateAmount = pixelate.blockSize;
        width *= pixelate.scale;
        height *= pixelate.scale;
      } else if (sequence.effect === "blur") {
        blurAmount = Math.max(0, Number(sequence.blurAmount) || 8) * level;
      }
    }

    return {
      sourceId: source,
      sourceUrl: getBrushUrl(source),
      centerX,
      centerY,
      width: Math.max(0.1, width),
      height: Math.max(0.1, height),
      rotation,
      opacity: clamp(opacity, 0, 1),
      blendMode: "normal",
      imageRendering: sequence?.effect === "pixelate" ? "pixelated" : "auto",
      tintLayers,
      pixelateAmount,
      blurAmount,
      phaseOffsetMs: spec.index * 137 + spec.motifId * 59,
      playbackRate: loopPlan.sourceRates.get(source) || 1
    };
  }

  function createGeneratorExportScene(specs, dimensions, background, loopPlan, transparentBackground = false) {
    const scaleX = dimensions.width / Math.max(1, state.currentWidth);
    const scaleY = dimensions.height / Math.max(1, state.currentHeight);
    const assetUsage = new Map();
    const addAsset = (source, spec) => {
      if (!source) {
        return;
      }
      const current = assetUsage.get(source) || { width: 1, height: 1 };
      current.width = Math.max(current.width, Math.ceil(spec.width * scaleX * 1.3));
      current.height = Math.max(current.height, Math.ceil(spec.height * scaleY * 1.3));
      assetUsage.set(source, current);
    };
    for (const spec of specs) {
      addAsset(spec.brush.source, spec);
      addAsset(spec.sequence?.alternateSource, spec);
    }
    const assets = Array.from(assetUsage, ([source, usage]) => ({
      id: source,
      url: getBrushUrl(source),
      kind: "gif",
      mimeType: "image/gif",
      targetWidth: usage.width,
      targetHeight: usage.height,
      frameIntervalMs: EXPORT_SOURCE_FRAME_INTERVAL_MS,
      imageSmoothing: true
    }));
    return {
      outputWidth: dimensions.width,
      outputHeight: dimensions.height,
      selectionBounds: {
        left: 0,
        top: 0,
        right: state.currentWidth,
        bottom: state.currentHeight
      },
      entries: specs.map((spec) => createGeneratorExportEntry(spec, 0, loopPlan)),
      background: {
        include: !transparentBackground,
        color: background,
        matteColor: transparentBackground ? "" : background
      },
      assets,
      memoryBudgetBytes: getExportRasterBudgetBytes()
    };
  }

  function parseExportColor(color) {
    const normalized = String(color || "").trim();
    const match = /^#([0-9a-f]{6})$/i.exec(normalized);
    const value = Number.parseInt(match?.[1] || "ffffff", 16);
    return [(value >> 16) & 255, (value >> 8) & 255, value & 255, 255];
  }

  function maskGeneratorCropMargin(data, width, height, background) {
    if (state.currentMarginMode !== "crop" || state.currentMargin <= 0) {
      return;
    }
    const marginX = Math.min(
      Math.floor(width / 2),
      Math.max(0, Math.round(state.currentMargin * width / Math.max(1, state.currentWidth)))
    );
    const marginY = Math.min(
      Math.floor(height / 2),
      Math.max(0, Math.round(state.currentMargin * height / Math.max(1, state.currentHeight)))
    );
    const [red, green, blue, alpha] = parseExportColor(background);
    const fillPixel = (offset) => {
      data[offset] = red;
      data[offset + 1] = green;
      data[offset + 2] = blue;
      data[offset + 3] = alpha;
    };
    for (let y = 0; y < height; y += 1) {
      const fullRow = y < marginY || y >= height - marginY;
      const startX = fullRow ? 0 : 0;
      const endX = fullRow ? width : marginX;
      for (let x = startX; x < endX; x += 1) {
        fillPixel((y * width + x) * 4);
      }
      if (!fullRow) {
        for (let x = width - marginX; x < width; x += 1) {
          fillPixel((y * width + x) * 4);
        }
      }
    }
  }

  function flattenRgbaOverBackground(data, background) {
    const [backgroundRed, backgroundGreen, backgroundBlue] = parseExportColor(background);
    for (let offset = 0; offset < data.length; offset += 4) {
      const alpha = data[offset + 3] / 255;
      const inverseAlpha = 1 - alpha;
      data[offset] = Math.round(data[offset] * alpha + backgroundRed * inverseAlpha);
      data[offset + 1] = Math.round(data[offset + 1] * alpha + backgroundGreen * inverseAlpha);
      data[offset + 2] = Math.round(data[offset + 2] * alpha + backgroundBlue * inverseAlpha);
      data[offset + 3] = 255;
    }
  }

  function compositeRgbaOver(base, overlay) {
    for (let offset = 0; offset < base.length; offset += 4) {
      const alpha = overlay[offset + 3] / 255;
      if (alpha <= 0) {
        continue;
      }
      const inverseAlpha = 1 - alpha;
      base[offset] = Math.round(overlay[offset] * alpha + base[offset] * inverseAlpha);
      base[offset + 1] = Math.round(overlay[offset + 1] * alpha + base[offset + 1] * inverseAlpha);
      base[offset + 2] = Math.round(overlay[offset + 2] * alpha + base[offset + 2] * inverseAlpha);
      base[offset + 3] = 255;
    }
  }

  function getValidRgbaPixels(output, width, height) {
    if (
      output?.kind !== "rgba" ||
      Number(output.width) !== width ||
      Number(output.height) !== height ||
      !(output.buffer instanceof ArrayBuffer) ||
      output.buffer.byteLength !== width * height * 4
    ) {
      throw new Error("The animation renderer returned an invalid frame");
    }
    return new Uint8ClampedArray(output.buffer);
  }

  function readFourCc(bytes, offset) {
    return String.fromCharCode(
      bytes[offset],
      bytes[offset + 1],
      bytes[offset + 2],
      bytes[offset + 3]
    );
  }

  function writeFourCc(bytes, offset, value) {
    for (let index = 0; index < 4; index += 1) {
      bytes[offset + index] = value.charCodeAt(index);
    }
  }

  function writeUint24LittleEndian(bytes, offset, value) {
    const normalized = clamp(Math.round(Number(value) || 0), 0, 0xffffff);
    bytes[offset] = normalized & 255;
    bytes[offset + 1] = (normalized >>> 8) & 255;
    bytes[offset + 2] = (normalized >>> 16) & 255;
  }

  function createWebpChunk(type, payloadParts, payloadLength) {
    const length = Math.max(0, Math.round(payloadLength));
    const header = new Uint8Array(8);
    writeFourCc(header, 0, type);
    new DataView(header.buffer).setUint32(4, length, true);
    const padding = length % 2 ? new Uint8Array(1) : null;
    return {
      byteLength: 8 + length + (padding ? 1 : 0),
      parts: padding
        ? [header, ...payloadParts, padding]
        : [header, ...payloadParts]
    };
  }

  function parseStillWebpFrame(buffer) {
    const bytes = new Uint8Array(buffer);
    if (
      bytes.byteLength < 20 ||
      readFourCc(bytes, 0) !== "RIFF" ||
      readFourCc(bytes, 8) !== "WEBP"
    ) {
      throw new Error("This browser could not encode a WebP frame");
    }
    const imageChunks = [];
    let chunkBytes = 0;
    let lossless = false;
    let foundImage = false;
    let offset = 12;
    while (offset + 8 <= bytes.byteLength) {
      const type = readFourCc(bytes, offset);
      const size = new DataView(bytes.buffer, bytes.byteOffset + offset + 4, 4)
        .getUint32(0, true);
      const paddedSize = size + (size % 2);
      const end = offset + 8 + paddedSize;
      if (end > bytes.byteLength) {
        throw new Error("This browser returned a damaged WebP frame");
      }
      if (type === "ALPH" || type === "VP8 " || type === "VP8L") {
        const chunk = bytes.subarray(offset, end);
        imageChunks.push(chunk);
        chunkBytes += chunk.byteLength;
        if (type === "VP8 " || type === "VP8L") {
          foundImage = true;
          lossless = type === "VP8L";
          break;
        }
      }
      offset = end;
    }
    if (!foundImage) {
      throw new Error("This browser did not provide a usable WebP image frame");
    }
    return { chunks: imageChunks, chunkBytes, lossless };
  }

  function createWebpFrameEncoder(width, height) {
    let canvas;
    let context;
    if (typeof OffscreenCanvas === "function") {
      canvas = new OffscreenCanvas(width, height);
      context = canvas.getContext("2d", { alpha: false, willReadFrequently: false });
    } else {
      canvas = document.createElement("canvas");
      canvas.width = width;
      canvas.height = height;
      context = canvas.getContext("2d", { alpha: false, willReadFrequently: false });
    }
    if (!context) {
      throw new Error("This browser cannot prepare WebP frames");
    }
    return async (pixels) => {
      context.putImageData(new ImageData(pixels, width, height), 0, 0);
      const blob = typeof canvas.convertToBlob === "function"
        ? await canvas.convertToBlob({ type: "image/webp", quality: 1 })
        : await canvasToBlob(canvas, "image/webp", 1);
      if (!blob || blob.type !== "image/webp") {
        throw new Error("This browser does not support full-quality WebP encoding");
      }
      return parseStillWebpFrame(await blob.arrayBuffer());
    };
  }

  function createAnimatedWebpBlob(frames, width, height, background) {
    if (!frames.length) {
      throw new Error("No WebP frames were rendered");
    }
    const vp8xPayload = new Uint8Array(10);
    vp8xPayload[0] = 0x02;
    writeUint24LittleEndian(vp8xPayload, 4, width - 1);
    writeUint24LittleEndian(vp8xPayload, 7, height - 1);
    const vp8xChunk = createWebpChunk("VP8X", [vp8xPayload], vp8xPayload.byteLength);

    const [red, green, blue, alpha] = parseExportColor(background);
    const animPayload = new Uint8Array([blue, green, red, alpha, 0, 0]);
    const animChunk = createWebpChunk("ANIM", [animPayload], animPayload.byteLength);
    const animationChunks = frames.map((frame) => {
      const frameHeader = new Uint8Array(16);
      writeUint24LittleEndian(frameHeader, 6, width - 1);
      writeUint24LittleEndian(frameHeader, 9, height - 1);
      writeUint24LittleEndian(frameHeader, 12, frame.delay);
      frameHeader[15] = 0x02;
      return createWebpChunk(
        "ANMF",
        [frameHeader, ...frame.chunks],
        frameHeader.byteLength + frame.chunkBytes
      );
    });

    const chunks = [vp8xChunk, animChunk, ...animationChunks];
    const totalLength = 12 + chunks.reduce((sum, chunk) => sum + chunk.byteLength, 0);
    if (totalLength - 8 > 0xffffffff) {
      throw new Error("This full-resolution animation exceeds WebP's 4 GB file limit");
    }
    const riffHeader = new Uint8Array(12);
    writeFourCc(riffHeader, 0, "RIFF");
    new DataView(riffHeader.buffer).setUint32(4, totalLength - 8, true);
    writeFourCc(riffHeader, 8, "WEBP");
    return new Blob(
      [riffHeader, ...chunks.flatMap((chunk) => chunk.parts)],
      { type: "image/webp" }
    );
  }

  async function renderGeneratorFramePixels(
    session,
    regularSpecs,
    uncroppedSpecs,
    timeMs,
    loopPlan,
    dimensions,
    background
  ) {
    let pixels;
    if (regularSpecs.length) {
      const regularEntries = regularSpecs.map(
        (spec) => createGeneratorExportEntry(spec, timeMs, loopPlan)
      );
      const regularOutput = await session.renderFrame(timeMs, regularEntries);
      pixels = getValidRgbaPixels(
        regularOutput,
        dimensions.width,
        dimensions.height
      );
    } else {
      pixels = new Uint8ClampedArray(dimensions.width * dimensions.height * 4);
    }
    if (uncroppedSpecs.length) {
      flattenRgbaOverBackground(pixels, background);
    }
    maskGeneratorCropMargin(pixels, dimensions.width, dimensions.height, background);
    if (uncroppedSpecs.length) {
      const uncroppedEntries = uncroppedSpecs.map(
        (spec) => createGeneratorExportEntry(spec, timeMs, loopPlan)
      );
      const uncroppedOutput = await session.renderFrame(timeMs, uncroppedEntries);
      const uncroppedPixels = getValidRgbaPixels(
        uncroppedOutput,
        dimensions.width,
        dimensions.height
      );
      compositeRgbaOver(pixels, uncroppedPixels);
    }
    return pixels;
  }

  async function renderGeneratorWebp(task, specs, background) {
    const metadataPlan = createGeneratorLoopPlan(specs);
    const dimensions = getGeneratorExportDimensions();
    const session = createGeneratorRasterSession(task, (message) => {
      if (message.action === "prepare" && Number(message.total) > 0) {
        updateGeneratorExportProgress(
          task,
          3 + 26 * (Number(message.completed) || 0) / Number(message.total),
          "Decoding"
        );
      }
    });
    try {
      const uncroppedSpecs = state.currentMarginMode === "crop"
        ? specs.filter((spec) => spec.uncropped)
        : [];
      const regularSpecs = uncroppedSpecs.length
        ? specs.filter((spec) => !spec.uncropped)
        : specs;
      const scene = createGeneratorExportScene(
        specs,
        dimensions,
        background,
        metadataPlan,
        uncroppedSpecs.length > 0
      );
      const prepared = await session.prepare(scene);
      throwIfExportCancelled(task);
      const decodedDurations = new Map(
        (prepared.assets || [])
          .filter((asset) => Number(asset.frameCount) > 1 && Number(asset.totalDurationMs) > 0)
          .map((asset) => [String(asset.id), Number(asset.totalDurationMs)])
      );
      const loopPlan = createGeneratorLoopPlan(
        specs,
        decodedDurations
      );
      const delays = createGeneratorFrameDelays(
        loopPlan.durationMs,
        getGeneratorExportFrameInterval(specs, loopPlan)
      );
      const encodeFrame = createWebpFrameEncoder(dimensions.width, dimensions.height);
      const frames = [];
      let elapsedMs = 0;
      for (let index = 0; index < delays.length; index += 1) {
        throwIfExportCancelled(task);
        const pixels = await renderGeneratorFramePixels(
          session,
          regularSpecs,
          uncroppedSpecs,
          elapsedMs,
          loopPlan,
          dimensions,
          background
        );
        throwIfExportCancelled(task);
        const encodedFrame = await encodeFrame(pixels);
        frames.push({ ...encodedFrame, delay: delays[index] });
        elapsedMs += delays[index];
        updateGeneratorExportProgress(
          task,
          30 + 67 * ((index + 1) / delays.length),
          "Rendering"
        );
      }
      session.release();
      if (task.rasterSession === session) {
        task.rasterSession = null;
      }
      throwIfExportCancelled(task);
      updateGeneratorExportProgress(task, 98, "Finishing");
      const blob = createAnimatedWebpBlob(
        frames,
        dimensions.width,
        dimensions.height,
        background
      );
      return {
        blob,
        width: dimensions.width,
        height: dimensions.height,
        durationMs: delays.reduce((sum, delay) => sum + delay, 0),
        frameCount: delays.length,
        fps: delays.length / Math.max(0.001, loopPlan.durationMs / 1000),
        lossless: frames.every((frame) => frame.lossless)
      };
    } finally {
      if (task.rasterSession === session) {
        session.release();
        task.rasterSession = null;
      }
    }
  }

  async function loadGeneratorMp4Muxer() {
    if (!mp4MuxerPromise) {
      mp4MuxerPromise = import(EXPORT_MP4_MUXER_URL).then((module) => {
        if (typeof module.Muxer !== "function" || typeof module.ArrayBufferTarget !== "function") {
          throw new Error("The MP4 packager did not initialize");
        }
        return module;
      }).catch((error) => {
        mp4MuxerPromise = null;
        throw error;
      });
    }
    return mp4MuxerPromise;
  }

  function getGeneratorMp4Bitrate(width, height) {
    return clamp(
      Math.round(width * height * EXPORT_MP4_FRAME_RATE * 0.18),
      1_500_000,
      48_000_000
    );
  }

  async function getGeneratorMp4EncoderConfig(width, height) {
    if (typeof VideoEncoder !== "function" || typeof VideoFrame !== "function") {
      throw new Error("MP4 export needs a browser with WebCodecs support");
    }
    const config = {
      codec: EXPORT_MP4_CODEC,
      width,
      height,
      bitrate: getGeneratorMp4Bitrate(width, height),
      framerate: EXPORT_MP4_FRAME_RATE,
      bitrateMode: "variable",
      latencyMode: "quality",
      avc: { format: "avc" }
    };
    let support;
    try {
      support = await VideoEncoder.isConfigSupported(config);
    } catch (error) {
      support = null;
    }
    if (!support?.supported) {
      throw new Error("This browser cannot encode H.264 MP4 at the current canvas size");
    }
    return { ...config, ...support.config, avc: { format: "avc" } };
  }

  async function renderGeneratorMp4(task, specs, background) {
    const { Muxer, ArrayBufferTarget } = await loadGeneratorMp4Muxer();
    throwIfExportCancelled(task);
    const dimensions = getGeneratorExportDimensions();
    const encodedWidth = dimensions.width + (dimensions.width % 2);
    const encodedHeight = dimensions.height + (dimensions.height % 2);
    const encoderConfig = await getGeneratorMp4EncoderConfig(encodedWidth, encodedHeight);
    const metadataPlan = createGeneratorLoopPlan(specs, null, EXPORT_MP4_DURATION_MS);
    const session = createGeneratorRasterSession(task, (message) => {
      if (message.action === "prepare" && Number(message.total) > 0) {
        updateGeneratorExportProgress(
          task,
          3 + 22 * (Number(message.completed) || 0) / Number(message.total),
          "Decoding"
        );
      }
    });
    let encoder = null;
    try {
      const uncroppedSpecs = state.currentMarginMode === "crop"
        ? specs.filter((spec) => spec.uncropped)
        : [];
      const regularSpecs = uncroppedSpecs.length
        ? specs.filter((spec) => !spec.uncropped)
        : specs;
      const scene = createGeneratorExportScene(
        specs,
        dimensions,
        background,
        metadataPlan,
        uncroppedSpecs.length > 0
      );
      const prepared = await session.prepare(scene);
      throwIfExportCancelled(task);
      const decodedDurations = new Map(
        (prepared.assets || [])
          .filter((asset) => Number(asset.frameCount) > 1 && Number(asset.totalDurationMs) > 0)
          .map((asset) => [String(asset.id), Number(asset.totalDurationMs)])
      );
      const loopPlan = createGeneratorLoopPlan(
        specs,
        decodedDurations,
        EXPORT_MP4_DURATION_MS
      );
      const target = new ArrayBufferTarget();
      const muxer = new Muxer({
        target,
        video: {
          codec: "avc",
          width: encodedWidth,
          height: encodedHeight,
          frameRate: EXPORT_MP4_FRAME_RATE
        },
        fastStart: "in-memory"
      });
      let encoderError = null;
      let queueWaiter = null;
      const wakeQueueWaiter = () => {
        if (queueWaiter) {
          const resolve = queueWaiter;
          queueWaiter = null;
          resolve();
        }
      };
      encoder = new VideoEncoder({
        output(chunk, metadata) {
          try {
            muxer.addVideoChunk(chunk, metadata);
          } catch (error) {
            encoderError = error instanceof Error ? error : new Error("MP4 packaging failed");
          }
          wakeQueueWaiter();
        },
        error(error) {
          encoderError = error instanceof Error ? error : new Error("H.264 encoding failed");
          wakeQueueWaiter();
        }
      });
      encoder.configure(encoderConfig);
      encoder.addEventListener("dequeue", wakeQueueWaiter);
      task.videoEncoder = encoder;

      const frameCanvas = new OffscreenCanvas(encodedWidth, encodedHeight);
      const frameContext = frameCanvas.getContext("2d", { alpha: false });
      if (!frameContext) {
        throw new Error("This browser cannot prepare MP4 video frames");
      }
      const frameCount = Math.round(
        EXPORT_MP4_DURATION_MS / 1000 * EXPORT_MP4_FRAME_RATE
      );
      for (let index = 0; index < frameCount; index += 1) {
        throwIfExportCancelled(task);
        if (encoderError) {
          throw encoderError;
        }
        const timeMs = index * 1000 / EXPORT_MP4_FRAME_RATE;
        const pixels = await renderGeneratorFramePixels(
          session,
          regularSpecs,
          uncroppedSpecs,
          timeMs,
          loopPlan,
          dimensions,
          background
        );
        frameContext.fillStyle = background;
        frameContext.fillRect(0, 0, encodedWidth, encodedHeight);
        frameContext.putImageData(
          new ImageData(pixels, dimensions.width, dimensions.height),
          0,
          0
        );
        const timestamp = Math.round(index * 1_000_000 / EXPORT_MP4_FRAME_RATE);
        const nextTimestamp = Math.round((index + 1) * 1_000_000 / EXPORT_MP4_FRAME_RATE);
        const frame = new VideoFrame(frameCanvas, {
          timestamp,
          duration: nextTimestamp - timestamp
        });
        try {
          encoder.encode(frame, { keyFrame: index % (EXPORT_MP4_FRAME_RATE * 2) === 0 });
        } finally {
          frame.close();
        }
        while (encoder.encodeQueueSize > 6 && !encoderError) {
          await Promise.race([
            new Promise((resolve) => {
              queueWaiter = resolve;
              if (encoder.encodeQueueSize <= 6 || encoderError) {
                wakeQueueWaiter();
              }
            }),
            new Promise((resolve) => window.setTimeout(resolve, 50))
          ]);
          throwIfExportCancelled(task);
        }
        updateGeneratorExportProgress(
          task,
          26 + 70 * ((index + 1) / frameCount),
          "Rendering MP4"
        );
      }
      throwIfExportCancelled(task);
      session.release();
      if (task.rasterSession === session) {
        task.rasterSession = null;
      }
      await encoder.flush();
      if (encoderError) {
        throw encoderError;
      }
      muxer.finalize();
      const blob = new Blob([target.buffer], { type: "video/mp4" });
      encoder.removeEventListener("dequeue", wakeQueueWaiter);
      encoder.close();
      encoder = null;
      task.videoEncoder = null;
      return {
        blob,
        width: dimensions.width,
        height: dimensions.height,
        encodedWidth,
        encodedHeight,
        durationMs: EXPORT_MP4_DURATION_MS,
        frameCount,
        fps: EXPORT_MP4_FRAME_RATE,
        bitrate: encoderConfig.bitrate,
        codec: encoderConfig.codec
      };
    } finally {
      if (task.rasterSession === session) {
        session.release();
        task.rasterSession = null;
      }
      if (encoder) {
        try {
          encoder.close();
        } catch (error) {
          // A failed or cancelled encoder may already be closed.
        }
      }
      if (task.videoEncoder === encoder) {
        task.videoEncoder = null;
      }
    }
  }

  function formatExportByteSize(bytes) {
    const megabytes = Math.max(0, Number(bytes) || 0) / 1000000;
    return `${megabytes.toFixed(megabytes >= 10 ? 1 : 2)}mb`;
  }

  function downloadGeneratorBlob(blob, filename) {
    const url = URL.createObjectURL(blob);
    const link = document.createElement("a");
    link.href = url;
    link.download = filename;
    link.style.display = "none";
    document.body.appendChild(link);
    link.click();
    link.remove();
    window.setTimeout(() => URL.revokeObjectURL(url), 15000);
  }

  async function exportCurrentComposition(format = "webp", options = {}) {
    if (format && typeof format === "object") {
      options = format;
      format = options.format || "webp";
    }
    const exportFormat = format === "mp4" ? "mp4" : "webp";
    if (!state.currentCount || state.generating || state.exportTask) {
      return null;
    }
    setCropInspectionActive(false);
    const task = createGeneratorExportTask(exportFormat);
    state.exportTask = task;
    state.lastExport = null;
    setGeneratorExportUi(true, task);
    const specs = state.currentSpecs.map((spec) => ({
      ...spec,
      brush: spec.brush,
      sequence: spec.sequence ? { ...spec.sequence } : null
    }));
    const background = state.currentBackground;
    try {
      const result = exportFormat === "mp4"
        ? await renderGeneratorMp4(task, specs, background)
        : await renderGeneratorWebp(task, specs, background);
      throwIfExportCancelled(task);
      if (!result?.blob) {
        throw new Error(`The ${exportFormat.toUpperCase()} encoder did not produce a file`);
      }
      const filename = `composition-${formatSeed(state.currentSeed)}.${exportFormat}`;
      if (options.download !== false) {
        downloadGeneratorBlob(result.blob, filename);
      }
      state.lastExport = {
        format: exportFormat === "mp4" ? "mp4" : "animated-webp",
        filename,
        size: result.blob.size,
        width: result.width,
        height: result.height,
        durationMs: result.durationMs,
        frameCount: result.frameCount,
        ...(exportFormat === "mp4" ? {
          bitrate: result.bitrate,
          codec: result.codec,
          encodedWidth: result.encodedWidth,
          encodedHeight: result.encodedHeight,
          fps: result.fps
        } : {
          lossless: result.lossless
        })
      };
      if (exportFormat === "mp4") {
        const paddedSize = result.encodedWidth !== result.width || result.encodedHeight !== result.height
          ? ` · ${result.encodedWidth}×${result.encodedHeight} encoded`
          : "";
        setActionStatus(
          `mp4 ready · 6.0s · ${result.fps}fps · ` +
          `${result.width}×${result.height} full resolution${paddedSize} · ` +
          formatExportByteSize(result.blob.size)
        );
      } else {
        setActionStatus(
          `webp ready · ${(result.durationMs / 1000).toFixed(1)}s loop · ` +
          `${result.width}×${result.height} full resolution · ` +
          `${result.lossless ? "lossless color · " : "full color · "}` +
          formatExportByteSize(result.blob.size)
        );
      }
      return options.returnBlob === true
        ? { ...state.lastExport, blob: result.blob }
        : { ...state.lastExport };
    } catch (error) {
      if (error?.name === "AbortError" || task.cancelled) {
        setActionStatus(`${exportFormat} export cancelled`);
        return null;
      }
      setActionStatus(error?.message || "could not export this composition", true);
      return null;
    } finally {
      task.rasterSession?.release();
      try {
        task.videoEncoder?.close();
      } catch (error) {
        // Cleanup is best effort after an encoder failure.
      }
      task.videoEncoder = null;
      if (state.exportTask === task) {
        state.exportTask = null;
      }
      setGeneratorExportUi(false);
    }
  }

  function fitCanvasToStage() {
    state.fitFrameId = null;
    const rect = elements.stageArea.getBoundingClientRect();
    const stageStyle = getComputedStyle(elements.stageArea);
    const horizontalPadding =
      (Number.parseFloat(stageStyle.paddingLeft) || 0) +
      (Number.parseFloat(stageStyle.paddingRight) || 0);
    const verticalPadding =
      (Number.parseFloat(stageStyle.paddingTop) || 0) +
      (Number.parseFloat(stageStyle.paddingBottom) || 0);
    const chromeHeight = 50;
    const availableWidth = Math.max(40, rect.width - horizontalPadding - 2);
    const availableHeight = Math.max(40, rect.height - verticalPadding - chromeHeight - 2);
    const scale = Math.min(
      availableWidth / state.currentWidth,
      availableHeight / state.currentHeight,
      1
    );
    const displayWidth = Math.max(1, Math.floor(state.currentWidth * scale));
    const displayHeight = Math.max(1, Math.floor(state.currentHeight * scale));
    elements.canvas.style.width = `${displayWidth}px`;
    elements.canvas.style.height = `${displayHeight}px`;
    elements.composition.style.width = `${state.currentWidth}px`;
    elements.composition.style.height = `${state.currentHeight}px`;
    elements.composition.style.transform = `scale(${displayWidth / state.currentWidth}, ${displayHeight / state.currentHeight})`;
  }

  function scheduleCanvasFit() {
    if (state.fitFrameId !== null) {
      cancelAnimationFrame(state.fitFrameId);
    }
    state.fitFrameId = requestAnimationFrame(fitCanvasToStage);
  }

  function applyMarginPresentation(settings) {
    const cropEnabled = settings.marginMode === "crop" && settings.margin > 0;
    elements.marginOverlay.hidden = !cropEnabled;
    elements.marginOverlay.style.borderWidth = cropEnabled ? `${settings.margin}px` : "0px";
    elements.canvas.classList.toggle("has-crop-margin", cropEnabled);
    elements.canvas.dataset.generatorMargin = String(settings.margin);
    elements.canvas.dataset.generatorMarginMode = settings.marginMode;
    updateCropInspectionUi();
  }

  function updateCanvasChrome(settings, seed, modeCounts, uniqueSourceCount, sequenceSummary) {
    const modeSummary = MODE_ORDER
      .filter((mode) => modeCounts[mode])
      .map((mode) => `${modeCounts[mode]} ${mode}`)
      .join(" · ");
    const sourceLabel = settings.sourceLabel || "ALL";
    const marginSummary = settings.margin > 0
      ? ` · ${formatInteger(settings.margin)}px ${settings.marginMode === "crop" ? "crop" : "placement"} margin`
      : "";
    const accessibleMargin = settings.margin > 0
      ? `${settings.margin} pixel ${settings.marginMode === "crop" ? "cropped" : "placement"} margin.`
      : "No canvas margin.";
    const sequenceText = sequenceSummary?.enabled
      ? ` · ${formatInteger(sequenceSummary.layerCount)} sequenced layers`
      : "";
    const accessibleSequence = sequenceSummary?.enabled
      ? `${sequenceSummary.layerCount} generated layers have randomized sequence effects.`
      : "No added sequence effects.";
    elements.dimensionBadge.textContent = `${formatInteger(settings.width)} × ${formatInteger(settings.height)}`;
    elements.canvasMeta.textContent = `seed ${formatSeed(seed)} · ${formatInteger(settings.count)} gifs · ${sourceLabel}${marginSummary}${sequenceText}`;
    elements.canvas.setAttribute(
      "aria-label",
      `Random composition with ${settings.count} GIFs on a ${settings.width} by ${settings.height} pixel canvas. ${accessibleMargin} ${accessibleSequence} ${modeSummary}.`
    );
    setStatus(
      `${formatInteger(settings.count)} placements · ${formatInteger(uniqueSourceCount)} distinct gifs · ${modeSummary}${marginSummary}${sequenceText}`
    );
  }

  function yieldForPaint() {
    return new Promise((resolve) => requestAnimationFrame(() => resolve()));
  }

  async function generateComposition(options = {}) {
    if (state.generating || state.exportTask) {
      return false;
    }
    const baseSettings = readSettings();
    if (!baseSettings.pool.length) {
      setStatus("no gifs are available in this source", true);
      return false;
    }
    if (!baseSettings.modes.length) {
      elements.emptyState.hidden = false;
      setStatus("enable at least one placement mode", true);
      return false;
    }
    if (
      baseSettings.sequence.enabled &&
      (!baseSettings.sequence.timings.length || (
        !GENERATION_RANDOM_TOGGLES.sequenceEffects?.checked &&
        !getCompatibleSequencePairs(
          baseSettings.sequence.effects,
          baseSettings.sequence.timings
        ).length
      ))
    ) {
      setStatus("enable a compatible sequence effect and trigger style", true);
      return false;
    }

    let historySnapshot = options.historySnapshot || null;
    if (!options.dynamic) {
      const pending = takePendingDynamicUpdate();
      if (!historySnapshot && options.recordHistory && state.currentCount) {
        historySnapshot = pending.snapshot || captureGeneratorSnapshot();
      }
    }

    const requestedSeed = parseSeed(options.seed);
    const seed = requestedSeed ?? randomSeed();
    if (!options.dynamic) {
      randomizeGenerationControls(seed);
    }
    const settings = options.dynamic ? baseSettings : readSettings();
    if (
      settings.sequence.enabled &&
      !getCompatibleSequencePairs(settings.sequence.effects, settings.sequence.timings).length
    ) {
      setStatus("enable a compatible sequence effect and trigger style", true);
      return false;
    }
    const random = createRandom(seed);
    setCropInspectionActive(false);
    const token = ++state.generationToken;
    state.generating = true;
    elements.generate.disabled = true;
    syncCurrentBookmarkUI();
    elements.canvas.setAttribute("aria-busy", "true");
    elements.emptyState.hidden = true;
    setStatus("building a new composition…");
    await yieldForPaint();

    try {
      const { points, modeCounts } = buildCompositionPoints(settings, random);
      const { specs, usedSources, fallbackSources } = buildVisualSpecs(
        points,
        settings,
        random,
        Array.isArray(options.preferredSources) ? options.preferredSources : []
      );
      if (Array.isArray(options.uncroppedIndices) && options.uncroppedIndices.length) {
        const uncroppedIndices = new Set(options.uncroppedIndices.map(Number));
        for (const spec of specs) {
          spec.uncropped = uncroppedIndices.has(Number(spec.index));
        }
      }
      const sequenceSummary = buildSequenceAssignments(specs, settings, seed);
      if (token !== state.generationToken) {
        return false;
      }

      const fragment = document.createDocumentFragment();
      for (let index = 0; index < specs.length; index += 1) {
        fragment.appendChild(createStampElement(specs[index], index));
        if (index > 0 && index % 100 === 0) {
          await yieldForPaint();
          if (token !== state.generationToken) {
            return false;
          }
        }
      }

      const background = options.preserveBackground
        ? state.currentBackground
        : chooseBackground(settings, random);
      state.currentFallbackSources = fallbackSources.slice();
      state.currentUsedSources = new Set(usedSources);
      state.loadFailureCount = 0;
      elements.composition.replaceChildren(fragment, elements.marginOverlay);
      state.currentWidth = settings.width;
      state.currentHeight = settings.height;
      state.currentMargin = settings.margin;
      state.currentMarginMode = settings.marginMode;
      elements.composition.style.width = `${settings.width}px`;
      elements.composition.style.height = `${settings.height}px`;
      applyMarginPresentation(settings);
      elements.canvas.style.backgroundColor = background;
      elements.canvas.style.setProperty("--generator-canvas", background);
      state.currentCount = specs.length;
      state.currentSeed = seed;
      state.currentSignature = buildSignature(specs);
      state.currentModeCounts = modeCounts;
      state.currentUniqueSourceCount = usedSources.size;
      state.currentSequenceEnabled = sequenceSummary.enabled;
      state.currentSequenceLayerCount = sequenceSummary.layerCount;
      state.currentSequenceEffectCounts = sequenceSummary.effectCounts;
      state.currentSequenceTimingCounts = sequenceSummary.timingCounts;
      state.currentSpecs = specs;
      state.currentSettingsUsed = createStoredSettings(settings);
      state.currentBackground = background;
      state.currentSequenceSummary = sequenceSummary;
      state.currentBookmarkId = "";
      elements.width.value = String(settings.width);
      elements.height.value = String(settings.height);
      elements.count.value = String(settings.count);
      updateRangeOutputs();
      state.currentControlState = captureControlState();
      pushHistorySnapshot(historySnapshot);
      updateCanvasChrome(settings, seed, modeCounts, usedSources.size, sequenceSummary);
      updateCropInspectionUi();
      scheduleCanvasFit();
      scheduleGeneratorPixelatePreview();
      syncCurrentBookmarkUI();
      renderBookmarkGallery();
      await flushActiveSessionSave();
      return true;
    } catch (error) {
      console.error("Could not generate composition", error);
      setStatus("could not build this composition — try again", true);
      return false;
    } finally {
      if (token === state.generationToken) {
        state.generating = false;
        updateGenerateAvailability();
        syncCurrentBookmarkUI();
        updateCropInspectionUi();
        elements.canvas.setAttribute("aria-busy", "false");
      }
    }
  }

  function getSummary() {
    return {
      catalogSize: state.catalog.length,
      canvasWidth: state.currentWidth,
      canvasHeight: state.currentHeight,
      margin: state.currentMargin,
      marginMode: state.currentMarginMode,
      count: state.currentCount,
      seed: formatSeed(state.currentSeed),
      signature: state.currentSignature,
      backgroundColor: state.currentBackground,
      modeCounts: { ...state.currentModeCounts },
      uniqueSourceCount: state.currentUniqueSourceCount,
      sourceMode: state.sourceMode,
      selectedCategories: getSelectedSourceValues("category"),
      selectedTags: getSelectedSourceValues("tag"),
      activePoolSize: getActiveCatalog().length,
      sequenceEnabled: state.currentSequenceEnabled,
      sequencePaused: state.sequencePaused,
      sequenceLayerCount: state.currentSequenceLayerCount,
      sequenceEffectCounts: { ...state.currentSequenceEffectCounts },
      sequenceTimingCounts: { ...state.currentSequenceTimingCounts },
      cropInspectionActive: state.cropInspectionActive,
      uncroppedCount: state.currentSpecs.filter((spec) => spec.uncropped).length,
      randomRanges: Object.fromEntries(
        Object.entries(state.currentSettingsUsed?.randomRanges || {}).map(([key, range]) => [key, { ...range }])
      ),
      sequenceRanges: Object.fromEntries(
        Object.entries(state.currentSettingsUsed?.sequence?.ranges || {}).map(([key, range]) => [key, { ...range }])
      ),
      generationRandomize: Object.fromEntries(
        Object.entries(GENERATION_RANDOM_TOGGLES).map(([key, toggle]) => [key, Boolean(toggle?.checked)])
      ),
      rangeRandomize: Object.fromEntries(
        Object.entries(RANGE_RANDOM_TOGGLES).map(([key, toggle]) => [key, Boolean(toggle?.checked)])
      ),
      bookmarkCount: state.bookmarks.length,
      bookmarkLimit: MAX_BOOKMARKS,
      bookmarkStoragePersisted: state.bookmarkStoragePersisted,
      historyDepth: state.history.length,
      historyLimit: MAX_HISTORY_ACTIONS,
      exporting: Boolean(state.exportTask),
      lastExport: state.lastExport ? { ...state.lastExport } : null,
      loadFailureCount: state.loadFailureCount
    };
  }

  function attachEvents() {
    [...RANDOM_RANGE_CONTROLS, ...SEQUENCE_RANGE_CONTROLS].forEach(
      attachRangePointerInteraction
    );
    for (const entry of SINGLE_RANGE_OUTPUTS) {
      entry.input?.addEventListener("input", () => {
        updateRangeOutput(entry);
        if (entry.input === elements.margin) {
          updateCropInspectionUi();
        }
        markSettingsPending();
      });
    }

    for (const control of RANDOM_RANGE_CONTROLS) {
      control.fixed?.addEventListener("input", () => {
        updateRandomRangeControl(control);
        markSettingsPending();
      });
      control.minimum?.addEventListener("input", () => {
        updateRandomRangeControl(control, "minimum");
        markSettingsPending();
      });
      control.maximum?.addEventListener("input", () => {
        updateRandomRangeControl(control, "maximum");
        markSettingsPending();
      });
    }

    for (const control of SEQUENCE_RANGE_CONTROLS) {
      control.minimum?.addEventListener("input", () => {
        updateRandomRangeControl(control, "minimum");
        markSettingsPending({ sequenceChange: control.key });
      });
      control.maximum?.addEventListener("input", () => {
        updateRandomRangeControl(control, "maximum");
        markSettingsPending({ sequenceChange: control.key });
      });
    }

    const handleSourceChange = () => {
      updateSourceSummary();
      if (getActiveCatalog().length) {
        markSettingsPending();
      } else {
        markSettingsPending({ preserveStatus: true });
      }
    };

    document.querySelectorAll(".generator-source-checkbox").forEach((input) => {
      input.addEventListener("change", handleSourceChange);
    });

    document.querySelectorAll("[data-source-action]").forEach((button) => {
      button.addEventListener("click", () => {
        const kind = button.dataset.sourceKind === "tag" ? "tag" : "category";
        const checked = button.dataset.sourceAction === "all";
        document.querySelectorAll(
          `.generator-source-checkbox[data-source-kind="${kind}"]`
        ).forEach((input) => {
          input.checked = checked;
        });
        handleSourceChange();
      });
    });

    const activateSourceTab = (mode, focus = false) => {
      setSourceMode(mode, { focus });
      if (getActiveCatalog().length) {
        markSettingsPending();
      } else {
        markSettingsPending({ preserveStatus: true });
      }
    };
    elements.categoryTab.addEventListener("click", () => activateSourceTab("category"));
    elements.tagTab.addEventListener("click", () => activateSourceTab("tag"));
    [elements.categoryTab, elements.tagTab].forEach((tab) => {
      tab.addEventListener("keydown", (event) => {
        let nextMode = null;
        if (event.key === "ArrowLeft" || event.key === "ArrowRight") {
          nextMode = state.sourceMode === "category" ? "tag" : "category";
        } else if (event.key === "Home") {
          nextMode = "category";
        } else if (event.key === "End") {
          nextMode = "tag";
        }
        if (!nextMode) {
          return;
        }
        event.preventDefault();
        activateSourceTab(nextMode, true);
      });
    });

    elements.width.addEventListener("change", () => {
      normalizeDimensionInputs("width");
      markSettingsPending();
    });
    elements.height.addEventListener("change", () => {
      normalizeDimensionInputs("height");
      markSettingsPending();
    });

    document.querySelectorAll("[data-canvas-size]").forEach((button) => {
      button.addEventListener("click", () => {
        const match = /^(\d+)x(\d+)$/.exec(button.dataset.canvasSize || "");
        if (!match) {
          return;
        }
        elements.width.value = match[1];
        elements.height.value = match[2];
        state.lockedAspectRatio = Number(match[1]) / Number(match[2]);
        normalizeDimensionInputs();
        markSettingsPending();
      });
    });

    document.querySelectorAll(".generator-mode-checkbox").forEach((input) => {
      input.addEventListener("change", markSettingsPending);
    });

    elements.sequenceEnabled.addEventListener("change", () => {
      updateSequenceControlUI();
      markSettingsPending({ sequenceChange: "enabled" });
    });

    document.querySelectorAll(
      ".generator-sequence-effect-checkbox, .generator-sequence-timing-checkbox"
    ).forEach((input) => {
      input.addEventListener("change", () => {
        updateSequenceControlUI();
        markSettingsPending({
          sequenceChange: input.classList.contains("generator-sequence-effect-checkbox")
            ? "effects"
            : "timings"
        });
      });
    });

    elements.sequencePause.addEventListener("click", () => {
      const historySnapshot = captureGeneratorSnapshot();
      setSequencePaused(!state.sequencePaused);
      state.currentBookmarkId = "";
      state.currentControlState = captureControlState();
      pushHistorySnapshot(historySnapshot);
      renderBookmarkGallery();
      syncCurrentBookmarkUI();
      void flushActiveSessionSave();
    });

    elements.cropInspect.addEventListener("click", () => {
      setCropInspectionActive(!state.cropInspectionActive);
    });

    elements.composition.addEventListener("click", (event) => {
      const image = event.target.closest?.(".generator-stamp");
      if (image) {
        toggleStampUncropped(image);
      }
    });

    elements.composition.addEventListener("keydown", (event) => {
      if (event.key !== "Enter" && event.key !== " ") {
        return;
      }
      const image = event.target.closest?.(".generator-stamp");
      if (!image || !state.cropInspectionActive) {
        return;
      }
      event.preventDefault();
      toggleStampUncropped(image);
    });

    elements.bookmark.addEventListener("click", () => {
      void bookmarkCurrentComposition();
    });

    elements.protectBookmarks.addEventListener("click", async () => {
      if (state.bookmarkSafetyBusy) {
        return;
      }
      state.bookmarkSafetyBusy = true;
      updateBookmarkSafetyUi();
      const persisted = await requestPersistentBookmarkStorage();
      state.bookmarkSafetyBusy = false;
      updateBookmarkSafetyUi();
      setActionStatus(
        persisted
          ? "bookmark storage protected by this browser"
          : "browser protection was not granted — keep a bookmark backup",
        !persisted
      );
    });

    elements.backupBookmarks.addEventListener("click", () => {
      void backupBookmarksToFile();
    });

    elements.restoreBookmarksButton.addEventListener("click", () => {
      elements.restoreBookmarks.click();
    });

    elements.restoreBookmarks.addEventListener("change", () => {
      const file = elements.restoreBookmarks.files?.[0];
      elements.restoreBookmarks.value = "";
      if (file) {
        void restoreBookmarksFromFile(file);
      }
    });

    elements.downloadWebp.addEventListener("click", () => {
      void exportCurrentComposition("webp");
    });

    elements.downloadMp4.addEventListener("click", () => {
      void exportCurrentComposition("mp4");
    });

    elements.exportCancel.addEventListener("click", cancelGeneratorExport);

    document.querySelectorAll('input[name="generatorMarginMode"]').forEach((input) => {
      input.addEventListener("change", () => {
        updateMarginModeUI();
        updateCropInspectionUi();
        markSettingsPending();
      });
    });

    Object.entries(RANDOM_TOGGLES).forEach(([key, toggle]) => {
      toggle?.addEventListener("change", () => {
        const rangeControl = RANDOM_RANGE_CONTROLS.find((control) => control.key === key);
        if (rangeControl) {
          updateRandomRangeControl(rangeControl);
        }
        syncRandomizeAllToggle();
        markSettingsPending({ affectsBackground: key === "background" });
      });
    });

    elements.randomizeAll.addEventListener("change", () => {
      const nextChecked = elements.randomizeAll.checked;
      Object.values(RANDOM_TOGGLES).forEach((toggle) => {
        if (toggle) {
          toggle.checked = nextChecked;
        }
      });
      RANDOM_RANGE_CONTROLS.forEach((control) => updateRandomRangeControl(control));
      syncRandomizeAllToggle();
      markSettingsPending({ affectsBackground: true });
    });

    for (const toggle of [
      ...Object.values(GENERATION_RANDOM_TOGGLES),
      ...Object.values(RANGE_RANDOM_TOGGLES)
    ]) {
      toggle?.addEventListener("change", () => {
        void commitFutureRandomizationControlChange();
      });
    }

    [elements.tintColor, elements.boxStyle].forEach((control) => {
      control.addEventListener("input", markSettingsPending);
      control.addEventListener("change", markSettingsPending);
    });
    elements.backgroundColor.addEventListener("input", () => {
      markSettingsPending({ affectsBackground: true });
    });
    elements.backgroundColor.addEventListener("change", () => {
      markSettingsPending({ affectsBackground: true });
    });

    elements.generate.addEventListener("click", () => {
      void generateComposition({ recordHistory: true });
    });

    elements.backgroundOnly.addEventListener("click", () => {
      void randomizeActiveBackground();
    });

    elements.undo.addEventListener("click", () => {
      void undoLastGeneratorAction();
    });

    elements.bookmarkGalleryMode.addEventListener("click", () => {
      setBookmarkGalleryMode(elements.bookmarksPanel.hidden, { focus: true });
    });

    elements.sidebarToggle.addEventListener("click", () => {
      const collapsed = elements.controls.classList.toggle("is-collapsed");
      elements.body.classList.toggle("generator-controls-collapsed", collapsed);
      elements.sidebarToggle.setAttribute("aria-expanded", String(!collapsed));
      elements.sidebarToggle.setAttribute(
        "aria-label",
        collapsed ? "Show generator controls" : "Hide generator controls"
      );
      scheduleCanvasFit();
    });

    document.addEventListener("keydown", (event) => {
      if (
        !event.defaultPrevented &&
        (event.metaKey || event.ctrlKey) &&
        !event.altKey &&
        !event.shiftKey &&
        String(event.key).toLowerCase() === "z"
      ) {
        event.preventDefault();
        void undoLastGeneratorAction();
        return;
      }
      if (event.key === "Escape" && state.exportTask) {
        event.preventDefault();
        cancelGeneratorExport();
        return;
      }
      if (
        event.defaultPrevented ||
        event.metaKey ||
        event.ctrlKey ||
        event.altKey ||
        String(event.key).toLowerCase() !== "r"
      ) {
        return;
      }
      const target = event.target;
      if (target instanceof HTMLInputElement || target instanceof HTMLSelectElement || target instanceof HTMLTextAreaElement) {
        return;
      }
      event.preventDefault();
      void generateComposition({ recordHistory: true });
    });

    window.addEventListener("resize", scheduleCanvasFit);
    window.addEventListener("pagehide", () => {
      void flushActiveSessionSave();
    });
    window.addEventListener("beforeunload", () => {
      state.exportTask?.cancel();
      revokeBookmarkObjectUrls();
    });
    if (typeof ResizeObserver === "function") {
      new ResizeObserver(scheduleCanvasFit).observe(elements.stageArea);
    }
  }

  async function initialize() {
    const folders = buildCatalog();
    if (!state.catalog.length) {
      setStatus("the stock gif catalog could not be loaded", true);
      elements.generate.disabled = true;
      return;
    }
    populateSourceFilters(folders);
    normalizeDimensionInputs();
    installRangeRandomizationToggles();
    updateRangeOutputs();
    setSourceMode("category");
    updateAspectLockUI();
    updateMarginModeUI();
    updateSequenceControlUI();
    setSequencePaused(false);
    setBookmarkGalleryMode(false);
    syncRandomizeAllToggle();
    attachEvents();
    syncCurrentBookmarkUI();
    await requestPersistentBookmarkStorage();
    await refreshBookmarks();
    state.currentWidth = normalizeInteger(elements.width.value, DEFAULT_WIDTH, CANVAS_MIN_SIZE, CANVAS_MAX_SIZE);
    state.currentHeight = normalizeInteger(elements.height.value, DEFAULT_HEIGHT, CANVAS_MIN_SIZE, CANVAS_MAX_SIZE);
    scheduleCanvasFit();
    const querySeed = parseSeed(new URLSearchParams(location.search).get("seed"));
    if (!(await restoreActiveSession())) {
      await generateComposition({ seed: querySeed });
    }
  }

  window.GeneratorApp = {
    generate(seed) {
      return generateComposition({ seed, recordHistory: true });
    },
    undo: undoLastGeneratorAction,
    randomizeBackground: randomizeActiveBackground,
    getSummary,
    exportWebp(options = {}) {
      return exportCurrentComposition("webp", options);
    },
    exportMp4(options = {}) {
      return exportCurrentComposition("mp4", options);
    },
    exportAnimation(options = {}) {
      return exportCurrentComposition("webp", options);
    },
    cancelExport: cancelGeneratorExport,
    get catalogSize() {
      return state.catalog.length;
    }
  };

  void initialize();
})();
