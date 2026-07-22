#!/usr/bin/env node

import { createReadStream, existsSync } from "node:fs";
import { writeFile } from "node:fs/promises";
import { createServer } from "node:http";
import { dirname, extname, isAbsolute, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, "../..");
const HARNESS_PATH = resolve(SCRIPT_DIRECTORY, "browser-performance-harness.js");

const MIME_TYPES = new Map([
  [".css", "text/css; charset=utf-8"],
  [".gif", "image/gif"],
  [".html", "text/html; charset=utf-8"],
  [".jpeg", "image/jpeg"],
  [".jpg", "image/jpeg"],
  [".js", "text/javascript; charset=utf-8"],
  [".json", "application/json; charset=utf-8"],
  [".mjs", "text/javascript; charset=utf-8"],
  [".png", "image/png"],
  [".svg", "image/svg+xml"],
  [".webp", "image/webp"]
]);

function parseArguments(argv) {
  const options = {
    url: "",
    stamps: 2000,
    headless: true,
    output: "",
    brushFile: resolve(PROJECT_ROOT, "bomb.png"),
    viewportWidth: 1280,
    viewportHeight: 800,
    pointerMoveSteps: 4,
    maxLongTaskMs: null,
    maxP95FrameGapMs: null,
    help: false
  };

  for (let index = 0; index < argv.length; index += 1) {
    const argument = argv[index];
    const value = argv[index + 1];
    if (argument === "--url") {
      options.url = value || "";
      index += 1;
    } else if (argument === "--stamps") {
      options.stamps = Math.max(1, Math.floor(Number(value) || 1));
      index += 1;
    } else if (argument === "--headful") {
      options.headless = false;
    } else if (argument === "--output") {
      options.output = value || "";
      index += 1;
    } else if (argument === "--brush-file") {
      options.brushFile = isAbsolute(value || "") ? value : resolve(process.cwd(), value || "");
      index += 1;
    } else if (argument === "--viewport") {
      const match = String(value || "").match(/^(\d+)x(\d+)$/i);
      if (!match) {
        throw new Error("--viewport must use WIDTHxHEIGHT, for example 1280x800.");
      }
      options.viewportWidth = Math.max(320, Number(match[1]));
      options.viewportHeight = Math.max(320, Number(match[2]));
      index += 1;
    } else if (argument === "--pointer-move-steps") {
      options.pointerMoveSteps = Math.max(1, Math.floor(Number(value) || 1));
      index += 1;
    } else if (argument === "--max-long-task-ms") {
      if (!Number.isFinite(Number(value))) {
        throw new Error("--max-long-task-ms requires a number.");
      }
      options.maxLongTaskMs = Math.max(0, Number(value));
      index += 1;
    } else if (argument === "--max-p95-frame-gap-ms") {
      if (!Number.isFinite(Number(value))) {
        throw new Error("--max-p95-frame-gap-ms requires a number.");
      }
      options.maxP95FrameGapMs = Math.max(0, Number(value));
      index += 1;
    } else if (argument === "--help" || argument === "-h") {
      options.help = true;
    } else {
      throw new Error(`Unknown argument: ${argument}`);
    }
  }
  return options;
}

function printHelp() {
  process.stdout.write(`
Usage: node scripts/tests/run-performance-regression.mjs [options]

Options:
  --stamps NUMBER                 Generate at least this many stamps (default: 2000)
  --headful                       Show Chromium instead of running headless
  --url URL                       Test an already-running server instead of serving the repo
  --brush-file PATH               Static image loaded through the file input (default: bomb.png)
  --viewport WIDTHxHEIGHT          Browser viewport (default: 1280x800)
  --pointer-move-steps NUMBER      Trusted mouse events per path segment (default: 4)
  --output PATH                    Also write the JSON report to this path
  --max-long-task-ms NUMBER        Optional failure threshold for the longest task
  --max-p95-frame-gap-ms NUMBER    Optional failure threshold for the p95 frame gap
  -h, --help                       Show this help
`);
}

async function loadPlaywright() {
  try {
    return await import("playwright");
  } catch (playwrightError) {
    try {
      return await import("playwright-core");
    } catch (coreError) {
      const error = new Error(
        "Playwright is not installed. Run `npm install --no-save --package-lock=false playwright` " +
          "and `npx playwright install chromium`, or use the dependency-free console harness."
      );
      error.cause = playwrightError;
      throw error;
    }
  }
}

function createStaticServer(rootDirectory) {
  const server = createServer((request, response) => {
    let pathname = "/";
    try {
      pathname = decodeURIComponent(new URL(request.url || "/", "http://127.0.0.1").pathname);
    } catch (error) {
      response.writeHead(400).end("Bad request");
      return;
    }
    const requestPath = pathname === "/" ? "/index.html" : pathname;
    const filePath = resolve(rootDirectory, `.${requestPath}`);
    const projectRelativePath = relative(rootDirectory, filePath);
    if (
      projectRelativePath === ".." ||
      projectRelativePath.startsWith(`..${sep}`) ||
      isAbsolute(projectRelativePath)
    ) {
      response.writeHead(403).end("Forbidden");
      return;
    }
    if (!existsSync(filePath)) {
      response.writeHead(404).end("Not found");
      return;
    }
    response.writeHead(200, {
      "Cache-Control": "no-store",
      "Content-Type": MIME_TYPES.get(extname(filePath).toLowerCase()) || "application/octet-stream"
    });
    const stream = createReadStream(filePath);
    stream.on("error", () => {
      if (!response.headersSent) {
        response.writeHead(500);
      }
      response.end("Read error");
    });
    stream.pipe(response);
  });

  return new Promise((resolveServer, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      resolveServer({
        server,
        url: `http://127.0.0.1:${address.port}/`
      });
    });
  });
}

async function executeTrustedGeneration(page, targetStampCount, pointerMoveSteps) {
  const before = await page.evaluate(() => globalThis.DrawingPerfHarness.markGenerationStart());
  const plan = await page.evaluate(
    (settings) => globalThis.DrawingPerfHarness.getGenerationPlan(settings),
    { targetStampCount, pointerMoveSteps }
  );
  await page.mouse.move(plan.start.x, plan.start.y);
  await page.mouse.down({ button: "left" });
  let reachedTarget = false;
  try {
    for (let index = 0; index < plan.points.length; index += 1) {
      const point = plan.points[index];
      await page.mouse.move(point.x, point.y, { steps: plan.pointerMoveSteps });
      const stampCount = await page.locator("#world > img.stamp").count();
      if (stampCount - before.stampCount >= plan.targetStampCount) {
        reachedTarget = true;
        break;
      }
    }
  } finally {
    await page.mouse.up({ button: "left" });
  }
  const result = await page.evaluate(() => globalThis.DrawingPerfHarness.markGenerationEnd());
  return { ...result, reachedTarget };
}

async function panWithTrustedMouse(page, direction, repetitions = 5) {
  const viewport = page.locator("#viewport");
  const rect = await viewport.boundingBox();
  if (!rect) {
    throw new Error("#viewport has no bounding box.");
  }
  const left = rect.x + 120;
  const right = rect.x + Math.min(rect.width - 120, 820);
  const y = rect.y + rect.height * 0.52;
  const startX = direction > 0 ? left : right;
  const endX = direction > 0 ? right : left;
  for (let index = 0; index < repetitions; index += 1) {
    await page.mouse.move(startX, y);
    await page.mouse.down({ button: "middle" });
    await page.mouse.move(endX, y, { steps: 5 });
    await page.mouse.up({ button: "middle" });
  }
  await page.evaluate(() => globalThis.DrawingPerfHarness.settleFrames(5));
}

async function runViewportCullingTest(page) {
  const before = await page.evaluate(() => globalThis.DrawingPerfHarness.snapshotScene());
  await panWithTrustedMouse(page, 1);
  const afterPan = await page.evaluate(() => globalThis.DrawingPerfHarness.snapshotScene());
  await panWithTrustedMouse(page, -1);
  const afterRestore = await page.evaluate(() => globalThis.DrawingPerfHarness.snapshotScene());
  return page.evaluate(
    ({ initial, panned, restored }) =>
      globalThis.DrawingPerfHarness.evaluateViewportCulling(initial, panned, restored),
    { initial: before, panned: afterPan, restored: afterRestore }
  );
}

async function runVisibilityTest(context, page, probeDurationMs = 650) {
  await page.bringToFront();
  await page.evaluate(() => globalThis.DrawingPerfHarness.setTopLayerSequenceEnabled(true));
  const active = await page.evaluate(
    (duration) => globalThis.DrawingPerfHarness.sampleMutationActivity(duration, "visibility-active"),
    probeDurationMs
  );

  const backgroundPage = await context.newPage();
  await backgroundPage.goto("about:blank");
  await backgroundPage.bringToFront();
  await new Promise((resolvePromise) => setTimeout(resolvePromise, 120));
  const hiddenState = await page.evaluate(() => document.visibilityState);
  if (hiddenState !== "hidden") {
    await backgroundPage.close();
    await page.bringToFront();
    return {
      pass: true,
      skipped: true,
      active,
      reason: `This Chromium mode kept the background page ${hiddenState}; run with --headful to exercise visibility pausing.`
    };
  }

  const hiddenProbeId = await page.evaluate(() =>
    globalThis.DrawingPerfHarness.startMutationProbe("visibility-hidden")
  );
  await new Promise((resolvePromise) => setTimeout(resolvePromise, probeDurationMs));
  const hidden = await page.evaluate(
    (id) => globalThis.DrawingPerfHarness.finishMutationProbe(id),
    hiddenProbeId
  );
  await backgroundPage.close();
  await page.bringToFront();
  await page.evaluate(() => globalThis.DrawingPerfHarness.settleFrames(3));
  const resumed = await page.evaluate(
    (duration) => globalThis.DrawingPerfHarness.sampleMutationActivity(duration, "visibility-resumed"),
    probeDurationMs
  );

  return {
    pass: active.mutationCount > 0 && hidden.mutationCount === 0 && resumed.mutationCount > 0,
    skipped: false,
    active,
    hidden,
    resumed
  };
}

async function runLifecycleReloadTest(page) {
  await page.evaluate(() => globalThis.DrawingPerfHarness.prepare({
    targetStampCount: 32,
    consistentSize: 20,
    spacing: 4,
    pointerMoveSteps: 1
  }));
  const initialCount = await page.locator("#world > img.stamp").count();
  if (initialCount < 600) {
    await executeTrustedGeneration(page, 600 - initialCount, 1);
  }
  // Establish a durable baseline first, then exercise the immediate-close delta.
  await page.waitForTimeout(1500);
  const beforeCount = await page.locator("#world > img.stamp").count();
  const delta = await executeTrustedGeneration(page, 32, 1);
  const expectedCount = await page.locator("#world > img.stamp").count();
  const sessionKey = "random-brush-drawer-session-v1";
  const quotaFailureInstalled = await page.evaluate((key) => {
    const originalSetItem = Storage.prototype.setItem;
    Storage.prototype.setItem = function setItemWithForcedSessionQuota(storageKey, value) {
      if (this === sessionStorage && storageKey === key) {
        throw new DOMException("Forced lifecycle quota regression.", "QuotaExceededError");
      }
      return originalSetItem.call(this, storageKey, value);
    };
    try {
      sessionStorage.setItem(key, "quota-probe");
      return false;
    } catch (error) {
      return error?.name === "QuotaExceededError";
    }
  }, sessionKey);

  await page.reload({ waitUntil: "domcontentloaded" });
  let restoreTimedOut = false;
  try {
    await page.waitForFunction(
      (count) => document.querySelectorAll("#world > img.stamp").length === count,
      expectedCount,
      { timeout: 8000 }
    );
  } catch (error) {
    restoreTimedOut = true;
  }
  const restored = await page.evaluate(async (key) => {
    const indexedDbKeys = await new Promise((resolve) => {
      const request = indexedDB.open("image-brush-session-cache", 1);
      request.onerror = () => resolve([]);
      request.onsuccess = () => {
        const database = request.result;
        const transaction = database.transaction("snapshots", "readonly");
        const keysRequest = transaction.objectStore("snapshots").getAllKeys();
        keysRequest.onerror = () => resolve([]);
        keysRequest.onsuccess = () => resolve(keysRequest.result.map(String));
        transaction.oncomplete = () => database.close();
      };
    });
    return {
      stampCount: document.querySelectorAll("#world > img.stamp").length,
      pointer: sessionStorage.getItem(`${key}-pointer`) || "",
      pendingPointer: sessionStorage.getItem(`${key}-pending-pointer`) || "",
      tabId: sessionStorage.getItem(`${key}-tab-id`) || "",
      inlineSnapshotPresent: sessionStorage.getItem(key) !== null,
      indexedDbKeys
    };
  }, sessionKey);
  return {
    pass:
      quotaFailureInstalled &&
      !restoreTimedOut &&
      delta.generatedCount >= 32 &&
      expectedCount > beforeCount &&
      restored.stampCount === expectedCount &&
      restored.pointer.startsWith("idb:") &&
      restored.pendingPointer === "" &&
      restored.inlineSnapshotPresent === false,
    quotaFailureInstalled,
    restoreTimedOut,
    beforeCount,
    expectedCount,
    generatedDeltaCount: delta.generatedCount,
    restored
  };
}

function summarizeFailures(report, options) {
  const failures = [];
  for (const [name, result] of Object.entries(report.functional)) {
    if (!result.skipped && result.pass !== true) {
      failures.push(`${name} failed`);
    }
  }
  if (report.pageErrors.length) {
    failures.push(`${report.pageErrors.length} uncaught page error(s)`);
  }
  if (
    options.maxLongTaskMs !== null &&
    report.telemetry.longTasks.maxDurationMs > options.maxLongTaskMs
  ) {
    failures.push(
      `longest task ${report.telemetry.longTasks.maxDurationMs.toFixed(1)}ms exceeded ${options.maxLongTaskMs}ms`
    );
  }
  if (
    options.maxP95FrameGapMs !== null &&
    report.telemetry.frames.p95Ms > options.maxP95FrameGapMs
  ) {
    failures.push(
      `p95 frame gap ${report.telemetry.frames.p95Ms.toFixed(1)}ms exceeded ${options.maxP95FrameGapMs}ms`
    );
  }
  return failures;
}

async function main() {
  const options = parseArguments(process.argv.slice(2));
  if (options.help) {
    printHelp();
    return;
  }
  if (!existsSync(options.brushFile)) {
    throw new Error(`Static brush file does not exist: ${options.brushFile}`);
  }

  const { chromium } = await loadPlaywright();
  let localServer = null;
  let browser = null;
  try {
    if (!options.url) {
      localServer = await createStaticServer(PROJECT_ROOT);
    }
    const targetUrl = options.url || localServer.url;
    browser = await chromium.launch({ headless: options.headless });
    const context = await browser.newContext({
      viewport: { width: options.viewportWidth, height: options.viewportHeight },
      reducedMotion: "no-preference"
    });
    const page = await context.newPage();
    const pageErrors = [];
    const consoleErrors = [];
    page.on("pageerror", (error) => pageErrors.push(error.stack || error.message || String(error)));
    page.on("console", (message) => {
      if (message.type() === "error") {
        consoleErrors.push(message.text());
      }
    });
    await page.route(/^https:\/\/fonts\.googleapis\.com\//, (route) =>
      route.fulfill({ status: 200, contentType: "text/css; charset=utf-8", body: "" })
    );
    await page.goto(targetUrl, { waitUntil: "domcontentloaded" });
    await page.waitForSelector(".stock-brush-button", { state: "attached", timeout: 30000 });
    await page.addScriptTag({ path: HARNESS_PATH });
    await page.evaluate(() => globalThis.DrawingPerfHarness.startTelemetry());

    const brushInput = page.locator("#brushInput");
    await brushInput.evaluate((input) => input.removeAttribute("webkitdirectory"));
    await brushInput.setInputFiles(options.brushFile);
    await page.waitForFunction(
      () => document.querySelector("#brushGallery .brush-thumb") && /Loaded 1 brush image/.test(document.getElementById("brushStatus")?.textContent || ""),
      null,
      { timeout: 30000 }
    );
    await page.evaluate((settings) => globalThis.DrawingPerfHarness.prepare(settings), {
      targetStampCount: options.stamps,
      consistentSize: 20,
      spacing: 4,
      pointerMoveSteps: options.pointerMoveSteps
    });

    const functional = {};
    await page.evaluate(() => globalThis.DrawingPerfHarness.beginPhase("stamp-generation"));
    const generation = await executeTrustedGeneration(page, options.stamps, options.pointerMoveSteps);
    const generationPhase = await page.evaluate(() => globalThis.DrawingPerfHarness.endPhase("stamp-generation"));
    functional.generation = {
      pass: generation.reachedTarget && generation.generatedCount >= options.stamps,
      ...generation
    };

    await page.evaluate(() => globalThis.DrawingPerfHarness.beginPhase("undo-redo"));
    functional.undoRedo = await page.evaluate(() => globalThis.DrawingPerfHarness.verifyUndoRedo());
    const undoRedoPhase = await page.evaluate(() => globalThis.DrawingPerfHarness.endPhase("undo-redo"));

    await page.evaluate(() => globalThis.DrawingPerfHarness.beginPhase("viewport-culling"));
    functional.viewportCulling = await runViewportCullingTest(page);
    const viewportCullingPhase = await page.evaluate(() => globalThis.DrawingPerfHarness.endPhase("viewport-culling"));

    await page.evaluate(() => globalThis.DrawingPerfHarness.beginPhase("sequence-scheduler"));
    functional.sequenceScheduler = await page.evaluate(() =>
      globalThis.DrawingPerfHarness.verifySequenceScheduler()
    );
    const sequenceSchedulerPhase = await page.evaluate(() =>
      globalThis.DrawingPerfHarness.endPhase("sequence-scheduler")
    );
    functional.sequenceRuntimeOptimizations = await page.evaluate(() =>
      globalThis.DrawingPerfHarness.verifySequenceRuntimeOptimizations()
    );

    await page.evaluate(() => globalThis.DrawingPerfHarness.beginPhase("page-visibility"));
    functional.pageVisibility = await runVisibilityTest(context, page);
    const pageVisibilityPhase = await page.evaluate(() =>
      globalThis.DrawingPerfHarness.endPhase("page-visibility")
    );

    const harnessVersion = await page.evaluate(() => globalThis.DrawingPerfHarness.VERSION);
    const telemetry = await page.evaluate(() => globalThis.DrawingPerfHarness.stopTelemetry());
    functional.lifecycleReload = await runLifecycleReloadTest(page);
    const cleanup = {
      cleaned: true,
      reason: "The isolated test context closes after lifecycle reload verification."
    };
    const report = {
      harnessVersion,
      targetUrl,
      options: {
        stamps: options.stamps,
        headless: options.headless,
        viewport: `${options.viewportWidth}x${options.viewportHeight}`,
        pointerMoveSteps: options.pointerMoveSteps,
        brushFile: options.brushFile,
        maxLongTaskMs: options.maxLongTaskMs,
        maxP95FrameGapMs: options.maxP95FrameGapMs
      },
      functional,
      generation,
      phases: {
        generation: generationPhase,
        undoRedo: undoRedoPhase,
        viewportCulling: viewportCullingPhase,
        sequenceScheduler: sequenceSchedulerPhase,
        pageVisibility: pageVisibilityPhase
      },
      telemetry,
      cleanup,
      pageErrors,
      consoleErrors
    };
    report.failures = summarizeFailures(report, options);
    report.pass = report.failures.length === 0;

    const json = `${JSON.stringify(report, null, 2)}\n`;
    process.stdout.write(json);
    if (options.output) {
      await writeFile(resolve(process.cwd(), options.output), json, "utf8");
    }
    if (!report.pass) {
      process.exitCode = 1;
    }
  } finally {
    await browser?.close();
    if (localServer) {
      await new Promise((resolveClose) => localServer.server.close(resolveClose));
    }
  }
}

main().catch((error) => {
  process.stderr.write(`${error.stack || error.message || error}\n`);
  process.exitCode = 1;
});
