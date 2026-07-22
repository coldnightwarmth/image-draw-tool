(function installDrawingPerformanceHarness(global) {
  "use strict";

  if (global.DrawingPerfHarness) {
    return;
  }

  const VERSION = "1.1.0";
  const STAMP_SELECTOR = "#world > img.stamp";
  const TRANSPARENT_STAMP_PREFIX = "data:image/gif;base64,R0lGODlhAQABA";
  const DEFAULTS = Object.freeze({
    targetStampCount: 2000,
    brushFolderId: "squares",
    consistentSize: 20,
    spacing: 4,
    pointerMoveSteps: 4,
    sequenceProbeMs: 900,
    inactiveProbeMs: 450,
    cullPanPixels: 3200,
    cleanup: true
  });

  const runtime = {
    telemetry: null,
    probes: new Map(),
    nextProbeId: 1,
    baselineNodes: [],
    generatedNodes: [],
    generatedSignatures: [],
    generationStartedAt: 0
  };

  function sleep(milliseconds) {
    return new Promise((resolve) => global.setTimeout(resolve, milliseconds));
  }

  async function settleFrames(frameCount = 3) {
    const count = Math.max(1, Math.floor(Number(frameCount) || 1));
    for (let index = 0; index < count; index += 1) {
      await new Promise((resolve) => global.requestAnimationFrame(resolve));
    }
  }

  async function waitFor(predicate, options = {}) {
    const timeoutMs = Math.max(1, Number(options.timeoutMs) || 10000);
    const intervalMs = Math.max(1, Number(options.intervalMs) || 25);
    const description = options.description || "condition";
    const startedAt = performance.now();
    let lastError = null;
    while (performance.now() - startedAt < timeoutMs) {
      try {
        const value = predicate();
        if (value) {
          return value;
        }
      } catch (error) {
        lastError = error;
      }
      await sleep(intervalMs);
    }
    const suffix = lastError ? ` (${lastError.message || lastError})` : "";
    throw new Error(`Timed out waiting for ${description}${suffix}.`);
  }

  function getStampNodes() {
    return Array.from(document.querySelectorAll(STAMP_SELECTOR));
  }

  function getStampSignature(stamp) {
    return [
      stamp.dataset.strokeId || "",
      stamp.dataset.brushUrl || "",
      stamp.style.left || "",
      stamp.style.top || "",
      stamp.style.width || "",
      stamp.style.height || "",
      stamp.style.transform || "",
      stamp.style.opacity || ""
    ].join("|");
  }

  function getMemorySnapshot() {
    const memory = performance.memory;
    if (!memory) {
      return null;
    }
    return {
      usedJSHeapSize: Number(memory.usedJSHeapSize) || 0,
      totalJSHeapSize: Number(memory.totalJSHeapSize) || 0,
      jsHeapSizeLimit: Number(memory.jsHeapSizeLimit) || 0
    };
  }

  function snapshotScene() {
    const stamps = getStampNodes();
    let culledStamps = 0;
    let culledTransparentSources = 0;
    let hiddenStamps = 0;
    let sequenceStateStamps = 0;
    for (const stamp of stamps) {
      const culled = stamp.dataset.viewportCulled === "true" || stamp.classList.contains("is-culled");
      if (culled) {
        culledStamps += 1;
        if ((stamp.getAttribute("src") || "").startsWith(TRANSPARENT_STAMP_PREFIX)) {
          culledTransparentSources += 1;
        }
      }
      if (stamp.classList.contains("is-layer-hidden")) {
        hiddenStamps += 1;
      }
      if (Object.keys(stamp.dataset).some((key) => key.startsWith("sequence"))) {
        sequenceStateStamps += 1;
      }
    }

    return {
      timestamp: performance.now(),
      visibilityState: document.visibilityState,
      stampCount: stamps.length,
      renderedStampCount: stamps.length - culledStamps - hiddenStamps,
      culledStampCount: culledStamps,
      culledTransparentSourceCount: culledTransparentSources,
      hiddenStampCount: hiddenStamps,
      sequenceStateStampCount: sequenceStateStamps,
      layerCount: document.querySelectorAll("#editLayerList .edit-layer-entry").length,
      worldChildCount: document.getElementById("world")?.childElementCount || 0,
      domElementCount: document.getElementsByTagName("*").length,
      domImageCount: document.images.length,
      memory: getMemorySnapshot()
    };
  }

  function percentile(values, ratio) {
    if (!values.length) {
      return 0;
    }
    const sorted = values.slice().sort((left, right) => left - right);
    const index = Math.max(0, Math.min(sorted.length - 1, Math.ceil(sorted.length * ratio) - 1));
    return sorted[index];
  }

  function summarizeFrameGaps(frameGaps) {
    const values = frameGaps.filter((value) => Number.isFinite(value) && value >= 0);
    return {
      sampleCount: values.length,
      meanMs: values.length ? values.reduce((sum, value) => sum + value, 0) / values.length : 0,
      p50Ms: percentile(values, 0.5),
      p95Ms: percentile(values, 0.95),
      p99Ms: percentile(values, 0.99),
      maxMs: values.length ? Math.max(...values) : 0,
      over32ms: values.filter((value) => value > 32).length,
      over50ms: values.filter((value) => value > 50).length,
      over100ms: values.filter((value) => value > 100).length
    };
  }

  function startTelemetry() {
    if (runtime.telemetry) {
      stopTelemetry();
    }

    const telemetry = {
      startedAt: performance.now(),
      endedAt: 0,
      startScene: snapshotScene(),
      startMemory: getMemorySnapshot(),
      frameGaps: [],
      lastFrameAt: 0,
      rafId: null,
      longTasks: [],
      longTaskObserver: null,
      longTaskSupported: false,
      phases: [],
      activePhase: null
    };

    const sampleFrame = (timestamp) => {
      if (!runtime.telemetry || runtime.telemetry !== telemetry) {
        return;
      }
      if (telemetry.lastFrameAt > 0 && telemetry.frameGaps.length < 20000) {
        telemetry.frameGaps.push(timestamp - telemetry.lastFrameAt);
      }
      telemetry.lastFrameAt = timestamp;
      telemetry.rafId = global.requestAnimationFrame(sampleFrame);
    };
    telemetry.rafId = global.requestAnimationFrame(sampleFrame);

    if (typeof PerformanceObserver === "function") {
      try {
        telemetry.longTaskObserver = new PerformanceObserver((list) => {
          for (const entry of list.getEntries()) {
            telemetry.longTasks.push({
              name: entry.name,
              startTime: entry.startTime,
              duration: entry.duration,
              attribution: Array.from(entry.attribution || []).map((item) => ({
                name: item.name || "",
                containerType: item.containerType || "",
                containerName: item.containerName || "",
                containerId: item.containerId || "",
                containerSrc: item.containerSrc || ""
              }))
            });
          }
        });
        telemetry.longTaskObserver.observe({ type: "longtask", buffered: false });
        telemetry.longTaskSupported = true;
      } catch (error) {
        telemetry.longTaskObserver = null;
      }
    }

    runtime.telemetry = telemetry;
    return {
      startedAt: telemetry.startedAt,
      longTaskSupported: telemetry.longTaskSupported,
      scene: telemetry.startScene
    };
  }

  function beginPhase(name) {
    if (!runtime.telemetry) {
      startTelemetry();
    }
    if (runtime.telemetry.activePhase) {
      endPhase(runtime.telemetry.activePhase.name);
    }
    runtime.telemetry.activePhase = {
      name: String(name || "unnamed"),
      startedAt: performance.now(),
      startScene: snapshotScene(),
      startFrameIndex: runtime.telemetry.frameGaps.length,
      startLongTaskIndex: runtime.telemetry.longTasks.length
    };
    return runtime.telemetry.activePhase.startedAt;
  }

  function endPhase(name) {
    const telemetry = runtime.telemetry;
    const phase = telemetry?.activePhase;
    if (!telemetry || !phase) {
      return null;
    }
    if (name && String(name) !== phase.name) {
      throw new Error(`Cannot end phase ${name}; active phase is ${phase.name}.`);
    }
    const endedAt = performance.now();
    const frameGaps = telemetry.frameGaps.slice(phase.startFrameIndex);
    const longTasks = telemetry.longTasks.slice(phase.startLongTaskIndex);
    const result = {
      name: phase.name,
      startedAt: phase.startedAt,
      endedAt,
      durationMs: endedAt - phase.startedAt,
      startScene: phase.startScene,
      endScene: snapshotScene(),
      frames: summarizeFrameGaps(frameGaps),
      longTasks: {
        count: longTasks.length,
        totalDurationMs: longTasks.reduce((sum, task) => sum + task.duration, 0),
        maxDurationMs: longTasks.length ? Math.max(...longTasks.map((task) => task.duration)) : 0
      }
    };
    telemetry.phases.push(result);
    telemetry.activePhase = null;
    return result;
  }

  function stopTelemetry() {
    const telemetry = runtime.telemetry;
    if (!telemetry) {
      return null;
    }
    if (telemetry.activePhase) {
      endPhase(telemetry.activePhase.name);
    }
    telemetry.endedAt = performance.now();
    if (telemetry.rafId !== null) {
      global.cancelAnimationFrame(telemetry.rafId);
    }
    telemetry.longTaskObserver?.disconnect();

    const resources = performance
      .getEntriesByType("resource")
      .filter((entry) => entry.startTime >= telemetry.startedAt);
    const navigationEntry = performance.getEntriesByType("navigation")[0] || null;
    const result = {
      version: VERSION,
      userAgent: navigator.userAgent,
      environment: {
        hardwareConcurrency: Number(navigator.hardwareConcurrency) || null,
        deviceMemoryGiB: Number(navigator.deviceMemory) || null,
        viewportWidth: global.innerWidth,
        viewportHeight: global.innerHeight,
        devicePixelRatio: global.devicePixelRatio
      },
      startedAt: telemetry.startedAt,
      endedAt: telemetry.endedAt,
      durationMs: telemetry.endedAt - telemetry.startedAt,
      startScene: telemetry.startScene,
      endScene: snapshotScene(),
      startMemory: telemetry.startMemory,
      endMemory: getMemorySnapshot(),
      frames: summarizeFrameGaps(telemetry.frameGaps),
      longTasks: {
        supported: telemetry.longTaskSupported,
        count: telemetry.longTasks.length,
        totalDurationMs: telemetry.longTasks.reduce((sum, task) => sum + task.duration, 0),
        maxDurationMs: telemetry.longTasks.length
          ? Math.max(...telemetry.longTasks.map((task) => task.duration))
          : 0,
        entries: telemetry.longTasks.slice()
      },
      resources: {
        count: resources.length,
        transferSize: resources.reduce((sum, entry) => sum + (Number(entry.transferSize) || 0), 0),
        decodedBodySize: resources.reduce((sum, entry) => sum + (Number(entry.decodedBodySize) || 0), 0)
      },
      navigation: navigationEntry
        ? {
            responseEndMs: navigationEntry.responseEnd,
            domInteractiveMs: navigationEntry.domInteractive,
            domContentLoadedMs: navigationEntry.domContentLoadedEventEnd,
            loadEventMs: navigationEntry.loadEventEnd,
            transferSize: navigationEntry.transferSize,
            decodedBodySize: navigationEntry.decodedBodySize
          }
        : null,
      phases: telemetry.phases.slice()
    };
    runtime.telemetry = null;
    return result;
  }

  function setRangeValue(selector, value) {
    const input = document.querySelector(selector);
    if (!(input instanceof HTMLInputElement)) {
      throw new Error(`Missing input ${selector}.`);
    }
    input.value = String(value);
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.dispatchEvent(new Event("change", { bubbles: true }));
  }

  function setCheckbox(selector, checked) {
    const input = document.querySelector(selector);
    if (!(input instanceof HTMLInputElement)) {
      throw new Error(`Missing checkbox ${selector}.`);
    }
    if (input.checked !== Boolean(checked)) {
      input.click();
    }
  }

  async function ensureBrushAvailable(options) {
    const currentThumb = document.querySelector("#brushGallery .brush-thumb");
    if (currentThumb) {
      return currentThumb;
    }

    document.getElementById("mainModeBrushButton")?.click();
    const folderId = String(options.brushFolderId || DEFAULTS.brushFolderId);
    const folderButton = await waitFor(
      () => Array.from(document.querySelectorAll("[data-stock-brush-folder-id]")).find(
        (button) => button.dataset.stockBrushFolderId === folderId
      ),
      { description: `stock brush folder ${folderId}` }
    );
    folderButton.click();
    return waitFor(
      () => document.querySelector("#brushGallery .brush-thumb"),
      { timeoutMs: 30000, description: "loaded brush preview" }
    );
  }

  async function prepare(options = {}) {
    const config = { ...DEFAULTS, ...options };
    await waitFor(
      () => document.getElementById("viewport") && document.querySelector(".stock-brush-button"),
      { timeoutMs: 30000, description: "application initialization" }
    );

    const thumb = await ensureBrushAvailable(config);
    const card = thumb.closest(".brush-item");
    if (card && !card.classList.contains("is-solo") && document.querySelectorAll(".brush-item").length > 1) {
      thumb.click();
    }

    document.getElementById("mainModeDrawButton")?.click();
    const pencilButton = document.querySelector('[data-draw-mode="pencil"]');
    if (pencilButton && pencilButton.getAttribute("aria-pressed") !== "true") {
      pencilButton.click();
    }
    const eraseButton = document.getElementById("eraseModeButton");
    if (eraseButton?.classList.contains("is-active") || eraseButton?.getAttribute("aria-pressed") === "true") {
      eraseButton.click();
    }
    setCheckbox("#randomSizeToggle", false);
    setCheckbox("#consistentToggle", true);
    setRangeValue("#consistentSizeSlider", config.consistentSize);
    setRangeValue("#spacingSlider", config.spacing);
    setRangeValue("#rotationSlider", 0);
    setRangeValue("#opacitySlider", 100);
    await settleFrames(3);
    return { config, scene: snapshotScene() };
  }

  function getGenerationPlan(options = {}) {
    const config = { ...DEFAULTS, ...options };
    const viewport = document.getElementById("viewport");
    if (!viewport) {
      throw new Error("Missing #viewport.");
    }
    const viewportRect = viewport.getBoundingClientRect();
    const controlsRect = document.getElementById("controls")?.getBoundingClientRect();
    const xMin = Math.max(viewportRect.left + 50, 60);
    const unobscuredRight = controlsRect && controlsRect.left > xMin + 180
      ? controlsRect.left - 35
      : viewportRect.right - 50;
    const xMax = Math.max(xMin + 180, Math.min(viewportRect.right - 50, unobscuredRight));
    const yMin = Math.max(viewportRect.top + 55, 65);
    const yMax = Math.max(yMin + 160, viewportRect.bottom - 55);
    const rowStep = Math.max(12, Math.min(36, Number(config.consistentSize) || 20));
    const horizontalDistance = Math.max(1, xMax - xMin);
    const estimatedRows = Math.ceil(
      (Math.max(1, Number(config.targetStampCount) || 1) * Math.max(1, Number(config.spacing) || 4)) /
        horizontalDistance
    );
    const rowsPerSweep = Math.max(1, Math.floor((yMax - yMin) / rowStep));
    const totalRows = Math.max(estimatedRows + 8, rowsPerSweep + 2);
    const points = [];
    for (let row = 0; row < totalRows; row += 1) {
      const sweep = Math.floor(row / rowsPerSweep);
      const rowInSweep = row % rowsPerSweep;
      const y = sweep % 2 === 0
        ? yMin + rowInSweep * rowStep
        : yMax - rowInSweep * rowStep;
      points.push({ x: row % 2 === 0 ? xMax : xMin, y });
    }
    return {
      start: { x: xMin, y: yMin },
      points,
      targetStampCount: Math.max(1, Math.floor(Number(config.targetStampCount) || 1)),
      pointerMoveSteps: Math.max(1, Math.floor(Number(config.pointerMoveSteps) || 1))
    };
  }

  function markGenerationStart() {
    runtime.baselineNodes = getStampNodes();
    runtime.generatedNodes = [];
    runtime.generatedSignatures = [];
    runtime.generationStartedAt = performance.now();
    return snapshotScene();
  }

  async function markGenerationEnd() {
    await settleFrames(3);
    const baseline = new Set(runtime.baselineNodes);
    runtime.generatedNodes = getStampNodes().filter((stamp) => !baseline.has(stamp));
    runtime.generatedSignatures = runtime.generatedNodes.map(getStampSignature);
    return {
      durationMs: performance.now() - runtime.generationStartedAt,
      baselineCount: runtime.baselineNodes.length,
      generatedCount: runtime.generatedNodes.length,
      scene: snapshotScene()
    };
  }

  function patchPointerCapture(element) {
    const methods = {
      setPointerCapture: element.setPointerCapture,
      releasePointerCapture: element.releasePointerCapture,
      hasPointerCapture: element.hasPointerCapture
    };
    element.setPointerCapture = function noOpSetPointerCapture() {};
    element.releasePointerCapture = function noOpReleasePointerCapture() {};
    element.hasPointerCapture = function noOpHasPointerCapture() { return false; };
    return () => {
      element.setPointerCapture = methods.setPointerCapture;
      element.releasePointerCapture = methods.releasePointerCapture;
      element.hasPointerCapture = methods.hasPointerCapture;
    };
  }

  function dispatchPointer(element, type, point, options = {}) {
    const button = Number.isFinite(Number(options.button)) ? Number(options.button) : 0;
    const buttons = Number.isFinite(Number(options.buttons))
      ? Number(options.buttons)
      : type === "pointerup"
      ? 0
      : button === 1
      ? 4
      : 1;
    const event = new PointerEvent(type, {
      bubbles: true,
      cancelable: true,
      composed: true,
      pointerId: Number(options.pointerId) || 41,
      pointerType: "mouse",
      isPrimary: true,
      clientX: point.x,
      clientY: point.y,
      button,
      buttons
    });
    element.dispatchEvent(event);
  }

  async function generateSyntheticStamps(options = {}) {
    const plan = getGenerationPlan(options);
    const viewport = document.getElementById("viewport");
    const restoreCapture = patchPointerCapture(viewport);
    let finalPoint = plan.start;
    markGenerationStart();
    try {
      dispatchPointer(viewport, "pointerdown", plan.start, { pointerId: 41, button: 0, buttons: 1 });
      for (let index = 0; index < plan.points.length; index += 1) {
        finalPoint = plan.points[index];
        dispatchPointer(viewport, "pointermove", finalPoint, {
          pointerId: 41,
          button: 0,
          buttons: 1
        });
        if (getStampNodes().length - runtime.baselineNodes.length >= plan.targetStampCount) {
          break;
        }
        if (index % 3 === 2) {
          await settleFrames(1);
        }
      }
      dispatchPointer(viewport, "pointerup", finalPoint, { pointerId: 41, button: 0, buttons: 0 });
    } finally {
      restoreCapture();
    }
    return markGenerationEnd();
  }

  async function verifyUndoRedo() {
    if (!runtime.generatedNodes.length) {
      throw new Error("No generated stamps were captured before undo/redo verification.");
    }
    const before = snapshotScene();
    const undoButton = document.getElementById("undoButton");
    const redoButton = document.getElementById("redoButton");
    if (!undoButton || undoButton.disabled) {
      throw new Error("Undo button is unavailable after generation.");
    }
    undoButton.click();
    await settleFrames(3);
    const afterUndo = snapshotScene();
    const generatedDetached = runtime.generatedNodes.every((stamp) => !stamp.isConnected);
    const undoPass =
      afterUndo.stampCount === runtime.baselineNodes.length && generatedDetached && !redoButton.disabled;

    redoButton.click();
    await settleFrames(3);
    const afterRedo = snapshotScene();
    const currentNodes = getStampNodes();
    const baselineSet = new Set(runtime.baselineNodes);
    const currentGenerated = currentNodes.filter((stamp) => !baselineSet.has(stamp));
    const identityPreserved =
      currentGenerated.length === runtime.generatedNodes.length &&
      currentGenerated.every((stamp, index) => stamp === runtime.generatedNodes[index]);
    const signaturesPreserved = currentGenerated.every(
      (stamp, index) => getStampSignature(stamp) === runtime.generatedSignatures[index]
    );
    const redoPass =
      afterRedo.stampCount === before.stampCount && identityPreserved && signaturesPreserved;

    return {
      pass: undoPass && redoPass,
      before,
      afterUndo,
      afterRedo,
      undoPass,
      redoPass,
      generatedDetached,
      identityPreserved,
      signaturesPreserved
    };
  }

  function evaluateViewportCulling(before, afterPan, afterRestore) {
    const allCulledUseTransparentSource =
      afterPan.culledStampCount > 0 &&
      afterPan.culledTransparentSourceCount === afterPan.culledStampCount;
    const restored =
      afterRestore.stampCount === before.stampCount && afterRestore.culledStampCount === 0;
    return {
      pass: afterPan.culledStampCount > 0 && allCulledUseTransparentSource && restored,
      before,
      afterPan,
      afterRestore,
      allCulledUseTransparentSource,
      restored
    };
  }

  async function panSynthetic(deltaX) {
    const viewport = document.getElementById("viewport");
    const rect = viewport.getBoundingClientRect();
    const start = { x: rect.left + Math.min(220, rect.width * 0.25), y: rect.top + rect.height * 0.5 };
    const end = { x: start.x + deltaX, y: start.y };
    const restoreCapture = patchPointerCapture(viewport);
    try {
      dispatchPointer(viewport, "pointerdown", start, { pointerId: 42, button: 1, buttons: 4 });
      dispatchPointer(viewport, "pointermove", end, { pointerId: 42, button: 1, buttons: 4 });
      dispatchPointer(viewport, "pointerup", end, { pointerId: 42, button: 1, buttons: 0 });
    } finally {
      restoreCapture();
    }
    await settleFrames(4);
  }

  async function verifyViewportCullingSynthetic(options = {}) {
    const distance = Math.max(2200, Number(options.cullPanPixels) || DEFAULTS.cullPanPixels);
    const before = snapshotScene();
    await panSynthetic(distance);
    const afterPan = snapshotScene();
    await panSynthetic(-distance);
    const afterRestore = snapshotScene();
    return evaluateViewportCulling(before, afterPan, afterRestore);
  }

  function isRelevantSequenceMutation(record) {
    if (record.type !== "attributes") {
      return false;
    }
    const target = record.target;
    if (!(target instanceof HTMLElement) || !target.classList.contains("stamp")) {
      return false;
    }
    const name = String(record.attributeName || "");
    return name === "style" || name === "src" || name === "class" || name.startsWith("data-sequence");
  }

  function startMutationProbe(label = "probe") {
    const id = runtime.nextProbeId;
    runtime.nextProbeId += 1;
    const probe = {
      id,
      label: String(label),
      startedAt: performance.now(),
      visibilityStateAtStart: document.visibilityState,
      mutationCount: 0,
      targets: new Set(),
      attributes: Object.create(null),
      visibilityTransitions: []
    };
    probe.observer = new MutationObserver((records) => {
      for (const record of records) {
        if (!isRelevantSequenceMutation(record)) {
          continue;
        }
        probe.mutationCount += 1;
        probe.targets.add(record.target);
        const name = String(record.attributeName || "unknown");
        probe.attributes[name] = (probe.attributes[name] || 0) + 1;
      }
    });
    const world = document.getElementById("world");
    probe.observer.observe(world, { subtree: true, attributes: true });
    probe.onVisibilityChange = () => {
      probe.visibilityTransitions.push({
        timestamp: performance.now(),
        visibilityState: document.visibilityState
      });
    };
    document.addEventListener("visibilitychange", probe.onVisibilityChange);
    runtime.probes.set(id, probe);
    return id;
  }

  function finishMutationProbe(id) {
    const probe = runtime.probes.get(Number(id));
    if (!probe) {
      throw new Error(`Unknown mutation probe ${id}.`);
    }
    probe.observer.disconnect();
    document.removeEventListener("visibilitychange", probe.onVisibilityChange);
    runtime.probes.delete(probe.id);
    return {
      id: probe.id,
      label: probe.label,
      startedAt: probe.startedAt,
      endedAt: performance.now(),
      durationMs: performance.now() - probe.startedAt,
      visibilityStateAtStart: probe.visibilityStateAtStart,
      visibilityStateAtEnd: document.visibilityState,
      visibilityTransitions: probe.visibilityTransitions,
      mutationCount: probe.mutationCount,
      mutatedStampCount: probe.targets.size,
      attributes: { ...probe.attributes }
    };
  }

  async function sampleMutationActivity(durationMs, label) {
    const id = startMutationProbe(label);
    await sleep(Math.max(1, Number(durationMs) || 1));
    return finishMutationProbe(id);
  }

  async function enableSequenceForTopLayer() {
    document.getElementById("mainModeEditButton")?.click();
    await settleFrames(2);
    const entry = await waitFor(
      () => document.querySelector("#editLayerList .edit-layer-entry"),
      { description: "generated edit layer" }
    );
    const sequenceButton = entry.querySelector(".edit-layer-sequence-button");
    if (sequenceButton?.getAttribute("aria-expanded") !== "true") {
      sequenceButton?.click();
      await settleFrames(2);
    }
    const refreshedEntry = document.querySelector("#editLayerList .edit-layer-entry");
    const addButton = refreshedEntry?.querySelector(".edit-layer-sequence-add-button");
    if (addButton) {
      addButton.click();
      await settleFrames(3);
    }
    const enabledButton = document.querySelector(
      "#editLayerList .edit-layer-entry .edit-layer-sequence-enable-button"
    );
    if (!enabledButton) {
      throw new Error("Could not create the sequence effect used by the scheduler test.");
    }
    if (enabledButton.getAttribute("aria-pressed") !== "true") {
      enabledButton.click();
      await settleFrames(3);
    }
    return true;
  }

  async function setTopLayerSequenceEnabled(enabled) {
    const button = document.querySelector(
      "#editLayerList .edit-layer-entry .edit-layer-sequence-enable-button"
    );
    if (!button) {
      throw new Error("Missing sequence enable button.");
    }
    const currentlyEnabled = button.getAttribute("aria-pressed") === "true";
    if (currentlyEnabled !== Boolean(enabled)) {
      button.click();
      await settleFrames(3);
    }
    return button.getAttribute("aria-pressed") === "true";
  }

  async function verifySequenceScheduler(options = {}) {
    const config = { ...DEFAULTS, ...options };
    const staticActivity = await sampleMutationActivity(config.inactiveProbeMs, "static-no-sequence");
    await enableSequenceForTopLayer();
    const activeActivity = await sampleMutationActivity(config.sequenceProbeMs, "sequence-active");
    await setTopLayerSequenceEnabled(false);
    const disabledActivity = await sampleMutationActivity(config.inactiveProbeMs, "sequence-disabled");
    await setTopLayerSequenceEnabled(true);
    const activeStampClassMutations = Number(activeActivity.attributes.class) || 0;
    const pass =
      staticActivity.mutationCount === 0 &&
      activeActivity.mutationCount > 0 &&
      activeStampClassMutations === 0 &&
      disabledActivity.mutationCount === 0;
    return {
      pass,
      activeStampClassMutations,
      staticActivity,
      activeActivity,
      disabledActivity
    };
  }

  function verifySequenceRuntimeOptimizations() {
    const requiredFunctions = [
      "getAdaptiveSequenceFrameIntervalMs",
      "getPulseLayerSequenceTriggers",
      "getWaveLayerSequenceTriggers",
      "normalizeLayerSequenceSettings"
    ];
    const missingFunctions = requiredFunctions.filter(
      (name) => typeof global[name] !== "function"
    );
    if (missingFunctions.length) {
      return {
        pass: false,
        missingFunctions
      };
    }

    const makeStroke = (count) => ({ elements: new Array(count) });
    const adaptiveIntervals = {
      small: global.getAdaptiveSequenceFrameIntervalMs([makeStroke(999)]),
      medium: global.getAdaptiveSequenceFrameIntervalMs([makeStroke(1000)]),
      large: global.getAdaptiveSequenceFrameIntervalMs([makeStroke(3000)]),
      hugeOffscreen: global.getAdaptiveSequenceFrameIntervalMs([makeStroke(8000)])
    };

    const pulseSettings = global.normalizeLayerSequenceSettings({
      pulseSpeed: 100,
      pulseRate: 100
    });
    const pulseStroke = { sequenceTopologyRevision: 0 };
    const pulseHost = { sequenceRuntime: null };
    const pulseBaseTime = 1000;
    let pulseTriggers = 0;
    for (let index = 0; index < 8; index += 1) {
      pulseTriggers += global.getPulseLayerSequenceTriggers(
        pulseStroke,
        index,
        8,
        pulseSettings,
        pulseBaseTime,
        120,
        pulseHost
      ).length;
    }
    let pulseCatchUpTriggers = 0;
    for (let index = 0; index < 8; index += 1) {
      pulseCatchUpTriggers += global.getPulseLayerSequenceTriggers(
        pulseStroke,
        index,
        8,
        pulseSettings,
        pulseBaseTime + 800,
        120,
        pulseHost
      ).length;
    }

    const waveSettings = global.normalizeLayerSequenceSettings({
      waveSpeed: 100,
      waveReverse: false
    });
    const waveStroke = { sequenceTopologyRevision: 0 };
    const waveHost = { sequenceRuntime: null };
    for (let index = 0; index < 6; index += 1) {
      global.getWaveLayerSequenceTriggers(
        waveStroke,
        index,
        6,
        waveSettings,
        pulseBaseTime,
        120,
        waveHost
      );
    }
    let waveCatchUpTriggers = 0;
    for (let index = 0; index < 6; index += 1) {
      waveCatchUpTriggers += global.getWaveLayerSequenceTriggers(
        waveStroke,
        index,
        6,
        waveSettings,
        pulseBaseTime + 100,
        120,
        waveHost
      ).length;
    }
    waveHost.sequenceRuntime.nextIndex = 999;
    waveHost.sequenceRuntime.nextTriggerTime = pulseBaseTime + 120;
    let rebasedWaveTriggers = 0;
    for (let index = 0; index < 3; index += 1) {
      rebasedWaveTriggers += global.getWaveLayerSequenceTriggers(
        waveStroke,
        index,
        3,
        waveSettings,
        pulseBaseTime + 120,
        120,
        waveHost
      ).length;
    }

    const pass =
      adaptiveIntervals.small === 0 &&
      adaptiveIntervals.medium === 25 &&
      Math.abs(adaptiveIntervals.large - 1000 / 30) < 0.01 &&
      adaptiveIntervals.hugeOffscreen === 50 &&
      pulseTriggers === 1 &&
      pulseCatchUpTriggers > 1 &&
      waveCatchUpTriggers > 1 &&
      rebasedWaveTriggers > 0 &&
      waveHost.sequenceRuntime.nextIndex >= 0 &&
      waveHost.sequenceRuntime.nextIndex < 3;
    return {
      pass,
      adaptiveIntervals,
      pulseTriggers,
      pulseCatchUpTriggers,
      waveCatchUpTriggers,
      rebasedWaveTriggers,
      rebasedWaveNextIndex: waveHost.sequenceRuntime.nextIndex
    };
  }

  async function cleanupGeneratedStroke() {
    if (!runtime.generatedNodes.some((stamp) => stamp.isConnected)) {
      return { cleaned: false, reason: "generated stroke is already detached" };
    }
    const undoButton = document.getElementById("undoButton");
    if (!undoButton || undoButton.disabled) {
      return { cleaned: false, reason: "undo is unavailable" };
    }
    undoButton.click();
    await settleFrames(3);
    return {
      cleaned: runtime.generatedNodes.every((stamp) => !stamp.isConnected),
      scene: snapshotScene()
    };
  }

  async function run(options = {}) {
    const config = { ...DEFAULTS, ...options };
    const results = {
      version: VERSION,
      config,
      warnings: [
        "Synthetic pointer events are used by the console runner. Use run-performance-regression.mjs for trusted browser input and visibility testing."
      ],
      functional: {}
    };
    await prepare(config);
    startTelemetry();

    beginPhase("stamp-generation");
    results.generation = await generateSyntheticStamps(config);
    results.phases = { generation: endPhase("stamp-generation") };
    results.functional.generation = {
      pass: results.generation.generatedCount >= config.targetStampCount,
      ...results.generation
    };

    beginPhase("undo-redo");
    results.functional.undoRedo = await verifyUndoRedo();
    results.phases.undoRedo = endPhase("undo-redo");

    beginPhase("viewport-culling");
    results.functional.viewportCulling = await verifyViewportCullingSynthetic(config);
    results.phases.viewportCulling = endPhase("viewport-culling");

    beginPhase("sequence-scheduler");
    results.functional.sequenceScheduler = await verifySequenceScheduler(config);
    results.phases.sequenceScheduler = endPhase("sequence-scheduler");
    results.functional.sequenceRuntimeOptimizations = verifySequenceRuntimeOptimizations();
    results.functional.pageVisibility = {
      pass: true,
      skipped: true,
      reason: "A page cannot make itself backgrounded; the Playwright runner performs this check."
    };

    results.telemetry = stopTelemetry();
    results.pass = Object.values(results.functional).every(
      (result) => result.pass === true || result.skipped === true
    );
    if (config.cleanup) {
      results.cleanup = await cleanupGeneratedStroke();
    }
    return results;
  }

  global.DrawingPerfHarness = Object.freeze({
    VERSION,
    DEFAULTS,
    prepare,
    snapshotScene,
    settleFrames,
    waitFor,
    startTelemetry,
    stopTelemetry,
    beginPhase,
    endPhase,
    getGenerationPlan,
    markGenerationStart,
    markGenerationEnd,
    generateSyntheticStamps,
    verifyUndoRedo,
    evaluateViewportCulling,
    verifyViewportCullingSynthetic,
    startMutationProbe,
    finishMutationProbe,
    sampleMutationActivity,
    enableSequenceForTopLayer,
    setTopLayerSequenceEnabled,
    verifySequenceScheduler,
    verifySequenceRuntimeOptimizations,
    cleanupGeneratedStroke,
    run
  });
})(globalThis);
