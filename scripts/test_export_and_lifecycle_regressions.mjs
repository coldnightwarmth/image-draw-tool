import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";

const appSource = fs.readFileSync(new URL("../app.js", import.meta.url), "utf8");

function extractFunction(name) {
  const functionStart = appSource.indexOf(`function ${name}(`);
  assert.notEqual(functionStart, -1, `missing function ${name}`);
  const start = appSource.slice(Math.max(0, functionStart - 6), functionStart) === "async "
    ? functionStart - 6
    : functionStart;
  const bodyStart = appSource.indexOf(") {", start) + 2;
  assert.ok(bodyStart > 1, `missing body for function ${name}`);
  let depth = 0;
  for (let index = bodyStart; index < appSource.length; index += 1) {
    if (appSource[index] === "{") {
      depth += 1;
    } else if (appSource[index] === "}") {
      depth -= 1;
      if (depth === 0) {
        return appSource.slice(start, index + 1);
      }
    }
  }
  throw new Error(`unterminated function ${name}`);
}

function rotatedBounds(left, top, width, height, rotation) {
  const radians = rotation * Math.PI / 180;
  const halfWidth = width / 2;
  const halfHeight = height / 2;
  const extentX = Math.abs(Math.cos(radians)) * halfWidth + Math.abs(Math.sin(radians)) * halfHeight;
  const extentY = Math.abs(Math.sin(radians)) * halfWidth + Math.abs(Math.cos(radians)) * halfHeight;
  const centerX = left + halfWidth;
  const centerY = top + halfHeight;
  return {
    left: centerX - extentX,
    right: centerX + extentX,
    top: centerY - extentY,
    bottom: centerY + extentY
  };
}

function makeElement(scenario, style, sequenceEnabled = true) {
  return {
    scenario,
    stroke: { enabled: sequenceEnabled, id: scenario.length },
    dataset: {
      sequenceActive: sequenceEnabled ? "1" : "0",
      rotation: "0",
      brushUrl: `${scenario}.gif`
    },
    style: {
      opacity: "1",
      imageRendering: "pixelated",
      ...style
    },
    currentSrc: `${scenario}.gif`,
    getAttribute(name) {
      return name === "src" ? this.currentSrc : null;
    }
  };
}

function testDynamicExportMembership() {
  const selection = { left: 0, top: 0, right: 100, bottom: 100 };
  const context = vm.createContext({
    Number,
    Math,
    performance: { now: () => 0 },
    clamp: (value, minimum, maximum) => Math.min(maximum, Math.max(minimum, value)),
    getStampLayerStroke: (element) => element.stroke,
    isLayerSequenceEnabled: (stroke) => stroke.enabled,
    getExportSequenceVisualState: (element, now) => ({
      opacity: 1,
      move: element.scenario === "move"
        ? { x: now >= 200 ? 100 : now >= 100 ? -70 : 0, y: 0 }
        : { x: 0, y: 0 },
      rotationOffset: element.scenario === "rotate" && now >= 100 ? 45 : 0,
      scale: element.scenario === "scale" && now >= 100 ? 2 : 1,
      groupedTransform: element.scenario === "group" && now >= 100
        ? { x: -40, y: 0, scale: 1, rotation: 0 }
        : null,
      tintSettings: { amountPercent: 0 },
      pixelateAmount: 0,
      blurAmount: 0,
      sourceUrl: element.dataset.brushUrl
    }),
    getStampGroupedLayerTransform: (_stroke, _element, transform) => transform,
    getStampLayerTransform: () => ({ x: 0, y: 0, scale: 1, rotation: 0 }),
    getStampWorldBoundsFromLayout: rotatedBounds,
    rectsIntersect: (left, right) => !(
      left.right <= right.left || left.left >= right.right ||
      left.bottom <= right.top || left.top >= right.bottom
    ),
    getLayerBlendMode: () => "normal",
    getStampBaseTintSettings: () => ({ amountPercent: 0 }),
    TRANSPARENT_STAMP_SRC: "transparent"
  });
  vm.runInContext(extractFunction("createExportStampEntry"), context);
  vm.runInContext(extractFunction("refreshExportSequenceEntries"), context);
  vm.runInContext(extractFunction("drawExportStampEntry"), context);

  const move = makeElement("move", { left: "150px", top: "40px", width: "20px", height: "20px" });
  const scale = makeElement("scale", { left: "101px", top: "40px", width: "10px", height: "10px" });
  const rotate = makeElement("rotate", { left: "101px", top: "30px", width: "4px", height: "40px" });
  const group = makeElement("group", { left: "130px", top: "40px", width: "20px", height: "20px" });
  const staticOutside = makeElement(
    "static-outside",
    { left: "150px", top: "40px", width: "20px", height: "20px" },
    false
  );
  const staticInside = makeElement(
    "static-inside",
    { left: "20px", top: "20px", width: "20px", height: "20px" },
    false
  );

  const candidates = [move, staticInside, scale, rotate, group].map((element) =>
    context.createExportStampEntry(element, selection, 0, { includeSequenceCandidates: true })
  );
  assert.equal(context.createExportStampEntry(
    staticOutside,
    selection,
    0,
    { includeSequenceCandidates: true }
  ), null, "fixed out-of-crop stamps should not inflate animated export work");
  assert.deepEqual(
    candidates.map((entry) => entry.isInSelection),
    [false, true, false, false, false],
    "moving candidates should be retained without being drawn before they enter"
  );

  const originalOrder = candidates.map((entry) => entry.element);
  context.refreshExportSequenceEntries(candidates, selection, 100);
  assert.deepEqual(
    candidates.map((entry) => entry.element),
    originalOrder,
    "dynamic membership must preserve DOM/layer ordering"
  );
  assert.deepEqual(
    candidates.map((entry) => entry.isInSelection),
    [true, true, true, true, true],
    "move, scale, rotate, and grouped transforms should all enter the crop dynamically"
  );

  const priorCenter = candidates[0].centerX;
  context.refreshExportSequenceEntries(candidates, selection, 200);
  assert.equal(candidates[0].isInSelection, false, "a stamp leaving the crop must stop drawing");
  assert.notEqual(candidates[0].centerX, priorCenter, "off-crop entries must not retain stale geometry");

  const throwingContext = new Proxy({}, {
    get() {
      throw new Error("off-crop entries should return before touching the canvas");
    }
  });
  context.drawExportStampEntry(throwingContext, selection, 1, 1, candidates[0]);
}

function makeStorage(initial = {}, failSnapshotWrites = false) {
  const values = new Map(Object.entries(initial));
  return {
    values,
    getItem(key) {
      return values.has(key) ? values.get(key) : null;
    },
    setItem(key, value) {
      if (failSnapshotWrites && key === "session") {
        throw new Error("quota exceeded");
      }
      values.set(key, String(value));
    },
    removeItem(key) {
      values.delete(key);
    }
  };
}

function makeLifecycleContext(options = {}) {
  const storage = makeStorage(
    { session: "old snapshot", pointer: options.initialPointer || "idb:old" },
    options.failSnapshotWrites !== false
  );
  let resolveWrite;
  let rejectWrite;
  let writeCount = 0;
  const writePromise = new Promise((resolve, reject) => {
    resolveWrite = resolve;
    rejectWrite = reject;
  });
  const context = vm.createContext({
    Number,
    Math,
    Date,
    JSON,
    SESSION_STORAGE_KEY: "session",
    SESSION_STORAGE_POINTER_KEY: "pointer",
    SESSION_STORAGE_PENDING_POINTER_KEY: "pending",
    SESSION_IDB_PREFIX: "idb:",
    SAVE_DIRECT_IDB_STAMP_THRESHOLD: 500,
    SESSION_PENDING_SNAPSHOT_RETRY_DELAYS_MS: [25, 75, 150, 300, 500],
    state: {
      saveRevision: 7,
      savedRevision: 6,
      saveEpoch: 3,
      saveFailureCount: 0
    },
    lastLifecycleFlushRevision: -1,
    snapshotDbConnection: {},
    sessionStorage: storage,
    getSessionTabId: () => "tab-1",
    beginSnapshotWriteToIndexedDb: () => {
      writeCount += 1;
      return writePromise;
    },
    writeSnapshotToIndexedDb: () => {
      writeCount += 1;
      return writePromise;
    },
    deleteSnapshotFromIndexedDb: async (key) => {
      context.deletedKeys.push(key);
    },
    readSnapshotFromIndexedDb: async () => {
      const snapshots = Array.isArray(options.pendingSnapshots)
        ? options.pendingSnapshots
        : [options.pendingSnapshot ?? null];
      const result = snapshots[Math.min(context.pendingReadCount, snapshots.length - 1)];
      context.pendingReadCount += 1;
      return result;
    },
    getSessionStorageItemSafe: (key) => storage.getItem(key),
    setSessionStorageItemSafe: (key, value) => {
      try {
        storage.setItem(key, value);
        return true;
      } catch {
        return false;
      }
    },
    removeSessionStorageItemSafe: (key) => storage.removeItem(key),
    buildSessionSnapshot: () => ({ version: 1, latest: true }),
    cancelScheduledSessionSave: () => {
      context.cancelCount += 1;
    },
    saveSessionStateNow: async () => {},
    cancelCount: 0,
    deletedKeys: [],
    pendingReadCount: 0,
    retryDelayCount: 0,
    window: {
      setTimeout(callback) {
        context.retryDelayCount += 1;
        Promise.resolve().then(callback);
      }
    }
  });
  for (const name of [
    "getLifecycleSnapshotKeyFromPointer",
    "cleanupSupersededLifecycleSnapshot",
    "saveSessionStateSynchronously",
    "persistLifecycleSessionSnapshot",
    "flushSessionSaveNow",
    "readPendingLifecycleSessionSnapshot",
    "persistSessionSnapshotJson"
  ]) {
    vm.runInContext(extractFunction(name), context);
  }
  return {
    context,
    storage,
    resolveWrite,
    rejectWrite,
    getWriteCount: () => writeCount
  };
}

async function settlePromises() {
  await Promise.resolve();
  await Promise.resolve();
}

async function testLifecyclePersistence() {
  const success = makeLifecycleContext({ initialPointer: "idb:tab-1:lifecycle:6:old" });
  success.context.flushSessionSaveNow({ type: "pagehide" });
  assert.equal(success.context.state.saveEpoch, 3, "pagehide must not obsolete an in-flight save epoch");
  assert.equal(success.getWriteCount(), 1, "the lifecycle IDB transaction should start immediately");
  assert.equal(success.storage.getItem("session"), "old snapshot", "fallback data stays until IDB commits");
  assert.match(success.storage.getItem("pending"), /^idb:tab-1:lifecycle:7:/);
  const olderPersisted = await success.context.persistSessionSnapshotJson("older snapshot", 1, 3, 6);
  assert.equal(olderPersisted, false, "an older in-flight save must not clear a pending lifecycle write");
  assert.match(success.storage.getItem("pending"), /^idb:tab-1:lifecycle:7:/);
  assert.equal(success.storage.getItem("pointer"), "idb:tab-1:lifecycle:6:old");
  success.context.flushSessionSaveNow({ type: "beforeunload" });
  assert.equal(success.getWriteCount(), 1, "beforeunload/pagehide for one revision should deduplicate");
  success.resolveWrite();
  await settlePromises();
  assert.equal(success.storage.getItem("session"), null, "committed lifecycle data replaces the old fallback");
  assert.equal(success.storage.getItem("pending"), null);
  assert.match(success.storage.getItem("pointer"), /^idb:tab-1:lifecycle:7:/);
  assert.equal(success.context.state.savedRevision, 7);
  assert.deepEqual(success.context.deletedKeys, ["tab-1:lifecycle:6:old"]);

  const failure = makeLifecycleContext({ initialPointer: "idb:tab-1:lifecycle:6:old" });
  failure.context.flushSessionSaveNow({ type: "pagehide" });
  failure.rejectWrite(new Error("IDB unavailable"));
  await settlePromises();
  assert.equal(failure.storage.getItem("pending"), null, "a failed pending write must not mask fallback data");
  assert.equal(failure.storage.getItem("session"), "old snapshot");
  assert.equal(failure.storage.getItem("pointer"), "idb:tab-1:lifecycle:6:old");
  assert.deepEqual(failure.context.deletedKeys, [], "the fallback key must survive a failed replacement");
  assert.equal(failure.context.lastLifecycleFlushRevision, -1, "a later lifecycle exit should retry a failed write");

  const superseded = makeLifecycleContext();
  superseded.context.flushSessionSaveNow({ type: "pagehide" });
  const supersededPointer = superseded.storage.getItem("pending");
  superseded.context.state.saveRevision = 8;
  superseded.resolveWrite();
  await settlePromises();
  assert.deepEqual(
    superseded.context.deletedKeys,
    [supersededPointer.slice("idb:".length)],
    "a lifecycle record superseded after BFCache return/edit should be deleted"
  );
  assert.equal(superseded.storage.getItem("pointer"), "idb:old");

  const stale = makeLifecycleContext({ failSnapshotWrites: false });
  stale.context.state.savedRevision = 9;
  const stalePersisted = await stale.context.persistSessionSnapshotJson("stale", 1, 3, 8);
  assert.equal(stalePersisted, false, "an older in-flight save must not overwrite a newer sync snapshot");
  assert.equal(stale.storage.getItem("session"), "old snapshot");

  const normalCommit = makeLifecycleContext({
    failSnapshotWrites: false,
    initialPointer: "idb:tab-1:lifecycle:6:old"
  });
  const normalPersisted = await normalCommit.context.persistSessionSnapshotJson("current", 1, 3, 7);
  assert.equal(normalPersisted, true);
  assert.deepEqual(
    normalCommit.context.deletedKeys,
    ["tab-1:lifecycle:6:old"],
    "a normal committed snapshot should clean up the superseded lifecycle record"
  );

  const pending = makeLifecycleContext({
    pendingSnapshots: [null, null, "latest snapshot"],
    initialPointer: "idb:tab-1:lifecycle:6:old"
  });
  pending.storage.setItem("pending", "idb:latest-key");
  const restored = await pending.context.readPendingLifecycleSessionSnapshot();
  assert.equal(restored, "latest snapshot", "restore should prefer a committed lifecycle snapshot");
  assert.equal(pending.context.pendingReadCount, 3, "restore should retry while the pagehide transaction commits");
  assert.equal(pending.context.retryDelayCount, 2);
  assert.equal(pending.storage.getItem("pointer"), "idb:latest-key");
  assert.equal(pending.storage.getItem("session"), null);
  assert.equal(pending.storage.getItem("pending"), null);
  assert.deepEqual(pending.context.deletedKeys, ["tab-1:lifecycle:6:old"]);

  const timedOutPending = makeLifecycleContext({
    pendingSnapshots: [null],
    initialPointer: "idb:tab-1:lifecycle:6:old"
  });
  timedOutPending.storage.setItem("pending", "idb:tab-1:lifecycle:7:uncommitted");
  assert.equal(await timedOutPending.context.readPendingLifecycleSessionSnapshot(), null);
  assert.deepEqual(
    timedOutPending.context.deletedKeys,
    ["tab-1:lifecycle:7:uncommitted"],
    "a pending record that misses the retry window should be deleted after any queued write"
  );
  assert.equal(timedOutPending.storage.getItem("pointer"), "idb:tab-1:lifecycle:6:old");
}

function testUrgentSessionSaveThrottle() {
  let now = 0;
  let nextTimerId = 1;
  let saveCount = 0;
  let normalQueueCount = 0;
  const timers = new Map();
  const microtasks = [];
  const context = vm.createContext({
    Number,
    Math,
    Infinity,
    SAVE_URGENT_MIN_INTERVAL_MS: 750,
    SAVE_DIRECT_IDB_STAMP_THRESHOLD: 500,
    state: {
      stampCount: 600,
      saveRevision: 0,
      saveFailureCount: 0,
      saveTimerId: null,
      saveIdleCallbackId: null,
      saveInFlight: false,
      saveUrgentPending: false,
      saveUrgentMicrotaskQueued: false,
      saveUrgentTimerId: null,
      saveUrgentLastStartedAt: -Infinity,
    },
    performance: { now: () => now },
    saveSessionStateNow: () => {
      if (context.state.saveInFlight) {
        return;
      }
      saveCount += 1;
    },
    queueSessionSave: () => {
      normalQueueCount += 1;
    },
    window: {
      setTimeout(callback, delay = 0) {
        const id = nextTimerId++;
        timers.set(id, { callback, dueAt: now + Math.max(0, Number(delay) || 0) });
        return id;
      },
      clearTimeout(id) {
        timers.delete(id);
      },
      cancelIdleCallback(id) {
        timers.delete(id);
      },
      queueMicrotask(callback) {
        microtasks.push(callback);
      },
    },
  });

  for (const name of [
    "cancelDeferredSessionSave",
    "cancelUrgentSessionSaveSchedule",
    "cancelScheduledSessionSave",
    "queueUrgentSessionSave",
    "scheduleSessionSave",
    "flushSessionSaveNow",
  ]) {
    vm.runInContext(extractFunction(name), context);
  }

  const flushMicrotasks = () => {
    while (microtasks.length) {
      microtasks.shift()();
    }
  };
  const advanceTo = (targetTime) => {
    while (true) {
      let nextId = null;
      let nextTimer = null;
      for (const [id, timer] of timers) {
        if (timer.dueAt <= targetTime && (!nextTimer || timer.dueAt < nextTimer.dueAt)) {
          nextId = id;
          nextTimer = timer;
        }
      }
      if (!nextTimer) {
        break;
      }
      now = nextTimer.dueAt;
      timers.delete(nextId);
      nextTimer.callback();
      flushMicrotasks();
    }
    now = targetTime;
  };

  for (let index = 0; index < 20; index += 1) {
    context.scheduleSessionSave();
  }
  assert.equal(microtasks.length, 1, "same-turn urgent mutations should coalesce");
  flushMicrotasks();
  assert.equal(saveCount, 1, "the first large-scene mutation must save immediately");
  assert.equal(context.state.saveUrgentLastStartedAt, 0);

  for (const eventTime of [100, 200, 300, 400, 500, 600, 700, 740]) {
    advanceTo(eventTime);
    context.scheduleSessionSave();
  }
  assert.equal(saveCount, 1);
  assert.equal(timers.size, 1, "continuous input should retain one trailing timer");
  assert.equal(
    Array.from(timers.values())[0].dueAt,
    750,
    "continuous input must not push back the fixed throttle deadline"
  );
  advanceTo(750);
  assert.equal(saveCount, 2, "the trailing save must run despite continuous input");

  context.state.saveInFlight = true;
  advanceTo(800);
  context.scheduleSessionSave();
  assert.equal(context.state.saveUrgentPending, true);
  assert.equal(timers.size, 0);
  context.state.saveInFlight = false;
  advanceTo(900);
  context.queueUrgentSessionSave();
  assert.equal(Array.from(timers.values())[0].dueAt, 1500);
  advanceTo(1500);
  assert.equal(saveCount, 3, "an in-flight mutation must receive a guaranteed trailing save");

  advanceTo(2400);
  context.scheduleSessionSave();
  assert.equal(microtasks.length, 1, "an edit after a quiet interval should regain leading immediacy");
  flushMicrotasks();
  assert.equal(saveCount, 4);

  context.state.saveInFlight = true;
  context.flushSessionSaveNow();
  assert.equal(saveCount, 4, "an in-flight hidden-page flush cannot overlap serialization");
  assert.equal(
    context.state.saveUrgentPending,
    true,
    "an in-flight hidden-page flush must preserve immediate trailing intent"
  );
  assert.equal(context.state.saveUrgentLastStartedAt, -Infinity);
  context.state.saveInFlight = false;
  context.queueUrgentSessionSave();
  flushMicrotasks();
  assert.equal(saveCount, 5, "the hidden-page trailing flush must bypass the normal throttle delay");

  advanceTo(2500);
  context.scheduleSessionSave();
  assert.equal(timers.size, 1);
  context.state.stampCount = 0;
  advanceTo(2510);
  context.scheduleSessionSave();
  assert.equal(context.state.saveUrgentPending, false);
  assert.equal(timers.size, 0, "dropping below the large-scene threshold must cancel urgent work");
  assert.equal(normalQueueCount, 1);
  advanceTo(4000);
  assert.equal(saveCount, 5, "cancelled urgent work must not produce a redundant save");
}

testDynamicExportMembership();
testUrgentSessionSaveThrottle();
await testLifecyclePersistence();
console.log("export membership and lifecycle persistence regression tests passed");
