#!/usr/bin/env node

import assert from "node:assert/strict";
import { createReadStream, existsSync, statSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { createServer } from "node:http";
import { dirname, extname, isAbsolute, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, "../..");
const MIME_TYPES = new Map([
  [".css", "text/css; charset=utf-8"],
  [".gif", "image/gif"],
  [".html", "text/html; charset=utf-8"],
  [".js", "text/javascript; charset=utf-8"],
  [".mjs", "text/javascript; charset=utf-8"],
  [".png", "image/png"],
  [".webp", "image/webp"]
]);

function createStaticServer(rootDirectory) {
  const server = createServer((request, response) => {
    let pathname;
    try {
      pathname = decodeURIComponent(new URL(request.url || "/", "http://127.0.0.1").pathname);
    } catch {
      response.writeHead(400).end("Bad request");
      return;
    }

    let requestPath = pathname;
    if (requestPath.endsWith("/")) {
      requestPath += "index.html";
    }
    let filePath = resolve(rootDirectory, `.${requestPath}`);
    const projectRelativePath = relative(rootDirectory, filePath);
    if (
      projectRelativePath === ".." ||
      projectRelativePath.startsWith(`..${sep}`) ||
      isAbsolute(projectRelativePath)
    ) {
      response.writeHead(403).end("Forbidden");
      return;
    }
    if (existsSync(filePath) && statSync(filePath).isDirectory()) {
      filePath = resolve(filePath, "index.html");
    }
    if (!existsSync(filePath) || !statSync(filePath).isFile()) {
      response.writeHead(404).end("Not found");
      return;
    }

    response.writeHead(200, {
      "Cache-Control": "no-store",
      "Content-Type": MIME_TYPES.get(extname(filePath).toLowerCase()) || "application/octet-stream"
    });
    if (request.method === "HEAD") {
      response.end();
      return;
    }
    const stream = createReadStream(filePath);
    stream.on("error", () => response.end("Read error"));
    stream.pipe(response);
  });

  return new Promise((resolveServer, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      resolveServer({ server, url: `http://127.0.0.1:${address.port}/` });
    });
  });
}

async function importPlaywright() {
  try {
    return await import("playwright");
  } catch (error) {
    const wrapped = new Error(
      "Playwright is required. Run `npm install --no-save --package-lock=false playwright` first."
    );
    wrapped.cause = error;
    throw wrapped;
  }
}

async function waitForGeneration(page, count) {
  await page.waitForFunction(
    (expectedCount) =>
      document.getElementById("generatorCanvas")?.getAttribute("aria-busy") === "false" &&
      document.querySelectorAll(".generator-stamp").length === expectedCount,
    count,
    { timeout: 20000 }
  );
}

async function waitForBookmarkCount(page, count) {
  await page.waitForFunction(
    (expectedCount) =>
      document.getElementById("generatorBookmarkCount")?.textContent === String(expectedCount) &&
      document.querySelectorAll(".generator-bookmark-card").length === expectedCount,
    count,
    { timeout: 10000 }
  );
}

async function waitForStampImages(page) {
  await page.waitForFunction(
    () => Array.from(document.querySelectorAll(".generator-stamp"))
      .every((image) => image.complete && image.naturalWidth > 0),
    null,
    { timeout: 20000 }
  );
}

async function setRange(page, selector, value) {
  await page.locator(selector).evaluate((input, nextValue) => {
    input.value = String(nextValue);
    input.dispatchEvent(new Event("input", { bubbles: true }));
  }, value);
}

async function setControlValue(page, selector, value) {
  await page.locator(selector).evaluate((input, nextValue) => {
    input.value = String(nextValue);
    input.dispatchEvent(new Event("input", { bubbles: true }));
    input.dispatchEvent(new Event("change", { bubbles: true }));
  }, value);
}

async function setCheckedValues(page, selector, selectedValues) {
  await page.locator(selector).evaluateAll((inputs, values) => {
    const selected = new Set(values);
    for (const input of inputs) {
      input.checked = selected.has(input.value);
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  }, selectedValues);
}

async function generateWithSeed(page, seed, count) {
  assert.equal(
    await page.evaluate((nextSeed) => window.GeneratorApp.generate(nextSeed), seed),
    true
  );
  await waitForGeneration(page, count);
}

async function getCompositionSnapshot(page) {
  return page.evaluate(() => {
    const canvas = document.getElementById("generatorCanvas");
    return {
      dimensions: [
        document.getElementById("generatorComposition")?.style.width,
        document.getElementById("generatorComposition")?.style.height
      ],
      background: canvas ? getComputedStyle(canvas).backgroundColor : "",
      margin: canvas?.dataset.generatorMargin || "",
      marginMode: canvas?.dataset.generatorMarginMode || "",
      stamps: Array.from(document.querySelectorAll(".generator-stamp")).map((stamp) => ({
        source: stamp.dataset.generatorSource,
        category: stamp.dataset.generatorCategory,
        mode: stamp.dataset.generatorMode,
        motif: stamp.dataset.generatorMotif,
        index: stamp.dataset.generatorIndex,
        x: stamp.dataset.generatorX,
        y: stamp.dataset.generatorY,
        size: stamp.dataset.generatorSize,
        rotation: stamp.dataset.generatorRotation,
        opacity: stamp.dataset.generatorOpacity,
        tintAmount: stamp.dataset.generatorTintAmount,
        uncropped: stamp.dataset.generatorUncropped,
        left: stamp.style.left,
        top: stamp.style.top,
        width: stamp.style.width,
        height: stamp.style.height,
        zIndex: stamp.style.zIndex,
        filter: stamp.style.filter,
        sequenceEffect: stamp.dataset.generatorSequenceEffect || "",
        sequenceTiming: stamp.dataset.generatorSequenceTiming || "",
        sequenceBase: stamp.dataset.generatorSequenceBaseSource || "",
        sequenceAlternate: stamp.dataset.generatorSequenceAlternateSource || "",
        sequenceDuration: stamp.style.getPropertyValue("--generator-sequence-duration"),
        sequenceDelay: stamp.style.getPropertyValue("--generator-sequence-delay"),
        sequenceMoveX: stamp.style.getPropertyValue("--generator-sequence-move-x"),
        sequenceMoveY: stamp.style.getPropertyValue("--generator-sequence-move-y"),
        sequenceRotation: stamp.style.getPropertyValue("--generator-sequence-rotation"),
        sequenceScale: stamp.style.getPropertyValue("--generator-sequence-scale"),
        sequenceFilterRest: stamp.style.getPropertyValue("--generator-sequence-filter-rest"),
        sequenceFilterActive: stamp.style.getPropertyValue("--generator-sequence-filter-active")
      }))
    };
  });
}

async function getControlSnapshot(page) {
  return page.evaluate(() => ({
    sourceMode: document.getElementById("generatorTagTab")?.getAttribute("aria-selected") === "true"
      ? "tag"
      : "category",
    selectedCategories: Array.from(document.querySelectorAll(
      '.generator-source-checkbox[data-source-kind="category"]:checked'
    )).map((input) => input.value),
    selectedTags: Array.from(document.querySelectorAll(
      '.generator-source-checkbox[data-source-kind="tag"]:checked'
    )).map((input) => input.value),
    dimensions: [
      document.getElementById("generatorCanvasWidthInput")?.value,
      document.getElementById("generatorCanvasHeightInput")?.value
    ],
    aspectLocked: document.getElementById("generatorAspectLockButton")?.getAttribute("aria-pressed"),
    margin: document.getElementById("generatorMarginSlider")?.value,
    marginMode: document.querySelector('input[name="generatorMarginMode"]:checked')?.value,
    count: document.getElementById("generatorCountSlider")?.value,
    modes: Array.from(document.querySelectorAll(".generator-mode-checkbox:checked"))
      .map((input) => input.value),
    randomize: Array.from(document.querySelectorAll(".generator-random-checkbox"))
      .map((input) => [input.id, input.checked]),
    generationRandomize: Array.from(document.querySelectorAll(
      "#generatorMarginRandomToggle, #generatorMarginModeRandomToggle, #generatorCountRandomToggle, #generatorSequenceEffectsRandomToggle"
    )).map((input) => [input.id, input.checked]),
    rangeRandomize: Array.from(document.querySelectorAll(".generator-range-random-checkbox"))
      .map((input) => [input.id, input.checked]),
    rangeEndpoints: Object.fromEntries(
      Array.from(document.querySelectorAll(".generator-dual-range input[type=range]"))
        .map((input) => [input.id, input.value])
    ),
    sequenceEnabled: document.getElementById("generatorSequenceEnabledToggle")?.checked,
    sequenceEffects: Array.from(document.querySelectorAll(".generator-sequence-effect-checkbox:checked"))
      .map((input) => input.value),
    sequenceTimings: Array.from(document.querySelectorAll(".generator-sequence-timing-checkbox:checked"))
      .map((input) => input.value),
    sequenceSpeed: document.getElementById("generatorSequenceSpeedSlider")?.value,
    sequenceIntensity: document.getElementById("generatorSequenceIntensitySlider")?.value,
    sequencePaused: document.getElementById("generatorSequencePauseButton")?.getAttribute("aria-pressed"),
    size: document.getElementById("generatorSizeSlider")?.value,
    spacing: document.getElementById("generatorSpacingSlider")?.value,
    rotation: document.getElementById("generatorRotationSlider")?.value,
    opacity: document.getElementById("generatorOpacitySlider")?.value,
    tintColor: document.getElementById("generatorTintColorInput")?.value,
    tintAmount: document.getElementById("generatorTintAmountSlider")?.value,
    boxStyle: document.getElementById("generatorBoxStyleSelect")?.value,
    backgroundColor: document.getElementById("generatorBackgroundColorInput")?.value
  }));
}

async function readBookmarkRecords(page) {
  return page.evaluate(() => new Promise((resolve, reject) => {
    const request = indexedDB.open("image-draw-generator-bookmarks", 1);
    request.onerror = () => reject(request.error);
    request.onsuccess = () => {
      const database = request.result;
      const transaction = database.transaction("compositions", "readonly");
      const getAll = transaction.objectStore("compositions").getAll();
      getAll.onerror = () => reject(getAll.error);
      getAll.onsuccess = () => {
        resolve(getAll.result
          .filter((record) => record.recordType !== "active-session")
          .map((record) => ({
          id: record.id,
          schemaVersion: record.schemaVersion,
          engineRevision: record.engineRevision,
          savedAt: record.savedAt,
          thumbnail: record.thumbnailBlob instanceof Blob
            ? { size: record.thumbnailBlob.size, type: record.thumbnailBlob.type }
            : null,
          controls: record.controls,
          composition: record.composition
        })));
        database.close();
      };
    };
  }));
}

async function readActiveSession(page) {
  return page.evaluate(() => new Promise((resolve, reject) => {
    const request = indexedDB.open("image-draw-generator-bookmarks", 1);
    request.onerror = () => reject(request.error);
    request.onsuccess = () => {
      const database = request.result;
      const transaction = database.transaction("compositions", "readonly");
      const get = transaction.objectStore("compositions").get("__active-generator-session__");
      get.onerror = () => reject(get.error);
      get.onsuccess = () => {
        resolve(get.result || null);
        database.close();
      };
    };
  }));
}

const { chromium } = await importPlaywright();
const localServer = await createStaticServer(PROJECT_ROOT);
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ viewport: { width: 1280, height: 800 } });
const page = await context.newPage();
const errors = [];
page.on("pageerror", (error) => errors.push(`page: ${error.message}`));
page.on("console", (message) => {
  if (message.type() === "error") {
    errors.push(`console: ${message.text()}`);
  }
});

try {
  await page.goto(`${localServer.url}generator/?seed=deadbeef`, { waitUntil: "domcontentloaded" });
  await waitForGeneration(page, 120);
  await waitForBookmarkCount(page, 0);
  await page.waitForFunction(() => !document.getElementById("generatorBookmarkButton")?.disabled);
  assert.equal((await page.evaluate(() => window.GeneratorApp.getSummary())).bookmarkLimit, 500);
  assert.ok([true, false, null].includes(
    (await page.evaluate(() => window.GeneratorApp.getSummary())).bookmarkStoragePersisted
  ));

  await setCheckedValues(
    page,
    '.generator-source-checkbox[data-source-kind="category"]',
    ["3d", "radial"]
  );
  await page.locator("#generatorTagTab").click();
  await setCheckedValues(
    page,
    '.generator-source-checkbox[data-source-kind="tag"]',
    ["live-action", "meme"]
  );
  await page.locator('[data-canvas-size="800x1200"]').click();
  await setRange(page, "#generatorMarginSlider", 88);
  await page.locator('.generator-margin-mode-choice:has(input[value="crop"]) span').click();
  await setRange(page, "#generatorCountSlider", 24);
  await page.locator("#generatorRandomizeAllToggle").uncheck({ force: true });
  await setRange(page, "#generatorSizeSlider", 74);
  await setRange(page, "#generatorSpacingSlider", 49);
  await setRange(page, "#generatorRotationSlider", 17);
  await setRange(page, "#generatorOpacitySlider", 83);
  await setControlValue(page, "#generatorTintColorInput", "#1a9cff");
  await setRange(page, "#generatorTintAmountSlider", 34);
  const savedRangeEndpoints = {
    generatorSizeRandomMinSlider: 31,
    generatorSizeRandomMaxSlider: 260,
    generatorSpacingRandomMinSlider: 6,
    generatorSpacingRandomMaxSlider: 900,
    generatorRotationRandomMinSlider: -42,
    generatorRotationRandomMaxSlider: 64,
    generatorOpacityRandomMinSlider: 17,
    generatorOpacityRandomMaxSlider: 91,
    generatorTintAmountRandomMinSlider: 11,
    generatorTintAmountRandomMaxSlider: 88,
    generatorSpraySpreadRandomMinSlider: 20,
    generatorSpraySpreadRandomMaxSlider: 1800,
    generatorLineAngleRandomMinSlider: -74,
    generatorLineAngleRandomMaxSlider: 112,
    generatorLineLengthRandomMinSlider: 20,
    generatorLineLengthRandomMaxSlider: 2600,
    generatorBoxWidthRandomMinSlider: 40,
    generatorBoxWidthRandomMaxSlider: 1900,
    generatorBoxHeightRandomMinSlider: 24,
    generatorBoxHeightRandomMaxSlider: 1700,
    generatorSequenceSpeedMinSlider: 31,
    generatorSequenceSpeedSlider: 82,
    generatorSequenceIntensityMinSlider: 20,
    generatorSequenceIntensitySlider: 140
  };
  for (const [id, value] of Object.entries(savedRangeEndpoints)) {
    await setRange(page, `#${id}`, value);
  }
  await setControlValue(page, "#generatorBoxStyleSelect", "filled");
  await setControlValue(page, "#generatorBackgroundColorInput", "#e8ddca");
  await setCheckedValues(page, ".generator-mode-checkbox", ["line", "box"]);
  await setCheckedValues(
    page,
    ".generator-sequence-effect-checkbox",
    ["rotate", "image-cycle"]
  );
  await setCheckedValues(page, ".generator-sequence-timing-checkbox", ["wave"]);
  await generateWithSeed(page, 0x51515151, 24);
  await waitForStampImages(page);
  await page.locator("#generatorCropInspectButton").click();
  await page.locator(".generator-stamp").first().evaluate((stamp) => stamp.click());
  await page.locator("#generatorCropInspectButton").click();
  await page.locator("#generatorSequencePauseButton").click();
  const savedFutureRandomizationIds = [
    "generatorMarginRandomToggle",
    "generatorMarginModeRandomToggle",
    "generatorCountRandomToggle",
    "generatorSequenceEffectsRandomToggle",
    "generatorSizeRangeRandomToggle",
    "generatorSequenceIntensityRangeRandomToggle"
  ];
  for (const id of savedFutureRandomizationIds) {
    await page.locator(`#${id}`).evaluate((input) => {
      input.checked = true;
      input.dispatchEvent(new Event("change", { bubbles: true }));
    });
  }

  const savedComposition = await getCompositionSnapshot(page);
  const savedControls = await getControlSnapshot(page);
  assert.equal(savedControls.sourceMode, "tag");
  assert.deepEqual([...savedControls.selectedCategories].sort(), ["3d", "radial"]);
  assert.deepEqual(savedControls.selectedTags, ["live-action", "meme"]);
  assert.equal(savedControls.sequencePaused, "true");
  assert.equal(savedComposition.stamps.length, 24);
  assert.equal(savedComposition.stamps.filter((spec) => spec.uncropped === "true").length, 1);
  assert.ok(savedComposition.stamps.every((spec) => spec.sequenceEffect));
  assert.deepEqual(
    Array.from(new Set(savedComposition.stamps.map((spec) => spec.sequenceEffect))).sort(),
    ["image-cycle", "rotate"]
  );

  await page.locator("#generatorBookmarkButton").click();
  await waitForBookmarkCount(page, 1);
  await page.waitForFunction(() => /bookmarked locally/i.test(
    document.getElementById("generatorActionStatus")?.textContent || ""
  ));
  assert.equal(await page.locator("#generatorBookmarkButton").getAttribute("aria-pressed"), "true");
  assert.equal((await page.locator("#generatorBookmarkButton span:last-child").textContent())?.trim(), "bookmarked");

  const records = await readBookmarkRecords(page);
  assert.equal(records.length, 1);
  assert.equal(records[0].schemaVersion, 1);
  assert.ok(records[0].engineRevision);
  assert.equal(records[0].composition.specs.length, 24);
  assert.equal(records[0].composition.specs.filter((spec) => spec.uncropped).length, 1);
  assert.ok(records[0].thumbnail?.size > 100, "expected a nonempty saved thumbnail");
  assert.match(records[0].thumbnail?.type || "", /^image\/(?:webp|png)$/);
  assert.deepEqual([...records[0].controls.selectedCategories].sort(), ["3d", "radial"]);
  assert.deepEqual(records[0].controls.selectedTags, ["live-action", "meme"]);
  assert.deepEqual(
    Object.fromEntries(
      Object.keys(savedRangeEndpoints).map((id) => [id, records[0].controls.ranges[id]])
    ),
    Object.fromEntries(
      Object.entries(savedRangeEndpoints).map(([id, value]) => [id, String(value)])
    )
  );
  assert.deepEqual(records[0].controls.generationRandomize, {
    margin: true,
    marginMode: true,
    count: true,
    sequenceEffects: true
  });
  assert.equal(records[0].controls.rangeRandomize.size, true);
  assert.equal(records[0].controls.rangeRandomize.sequenceIntensity, true);

  for (const id of savedFutureRandomizationIds) {
    await page.locator(`#${id}`).evaluate((input) => {
      input.checked = false;
      input.dispatchEvent(new Event("change", { bubbles: true }));
    });
  }

  await page.locator("#generatorBookmarkGalleryModeButton").click();
  assert.equal(await page.locator("#generatorControlsMain").isHidden(), true);
  assert.equal(await page.locator("#generatorBookmarksPanel").isVisible(), true);
  assert.equal(await page.locator("#generatorBookmarkGalleryModeButton").getAttribute("aria-pressed"), "true");

  await page.locator(".generator-bookmark-details").evaluate((details) => {
    details.open = true;
  });
  const downloadPromise = page.waitForEvent("download");
  await page.locator("#generatorBackupBookmarksButton").click();
  const backupDownload = await downloadPromise;
  const bookmarkBackupPath = await backupDownload.path();
  assert.ok(bookmarkBackupPath, "expected the bookmark backup to download");
  const bookmarkBackup = JSON.parse(await readFile(bookmarkBackupPath, "utf8"));
  assert.equal(bookmarkBackup.format, "image-draw-generator-bookmarks");
  assert.equal(bookmarkBackup.version, 1);
  assert.equal(bookmarkBackup.bookmarkCount, 1);
  assert.equal(bookmarkBackup.bookmarks[0].id, records[0].id);
  assert.match(bookmarkBackup.bookmarks[0].thumbnailDataUrl, /^data:image\/(?:webp|png);base64,/);

  await page.locator(".generator-bookmark-details").evaluate((details) => {
    details.open = true;
  });
  await page.waitForFunction(() => {
    const image = document.querySelector(".generator-bookmark-preview");
    return image instanceof HTMLImageElement && image.complete && image.naturalWidth > 0;
  });
  const thumbnailStats = await page.locator(".generator-bookmark-preview").evaluate((image) => {
    const canvas = document.createElement("canvas");
    canvas.width = image.naturalWidth;
    canvas.height = image.naturalHeight;
    const context = canvas.getContext("2d");
    context.drawImage(image, 0, 0);
    const pixels = context.getImageData(0, 0, canvas.width, canvas.height).data;
    const colors = new Set();
    const stride = Math.max(4, Math.floor(pixels.length / 12000 / 4) * 4);
    for (let index = 0; index < pixels.length; index += stride) {
      colors.add(`${pixels[index]},${pixels[index + 1]},${pixels[index + 2]}`);
      if (colors.size > 8) {
        break;
      }
    }
    return {
      colorCount: colors.size,
      width: image.naturalWidth,
      height: image.naturalHeight
    };
  });
  assert.ok(thumbnailStats.colorCount > 2, "expected the bookmark thumbnail to contain rendered GIFs");
  assert.ok(
    Math.abs(thumbnailStats.width / thumbnailStats.height - 2 / 3) < 0.01,
    "expected the portrait bookmark thumbnail to preserve its aspect ratio"
  );

  await page.locator("#generatorBookmarkGalleryModeButton").click();
  assert.equal(await page.locator("#generatorControlsMain").isVisible(), true);
  assert.equal(await page.locator("#generatorBookmarksPanel").isHidden(), true);
  assert.equal(await page.locator("#generatorBookmarkGalleryModeButton").getAttribute("aria-pressed"), "false");

  await generateWithSeed(page, 0x61616161, 24);
  assert.notDeepEqual((await getCompositionSnapshot(page)).stamps, savedComposition.stamps);
  await setCheckedValues(
    page,
    '.generator-source-checkbox[data-source-kind="tag"]',
    ["meme"]
  );
  await page.locator("#generatorCategoryTab").click();
  await page.locator("#generatorSequenceEnabledToggle").uncheck({ force: true });
  await setCheckedValues(page, ".generator-mode-checkbox", []);
  assert.equal(await page.evaluate(() => window.GeneratorApp.generate(0x71717171)), false);
  assert.equal(await page.locator("#generatorEmptyState").isVisible(), true);

  await page.locator("#generatorBookmarkGalleryModeButton").click();
  await page.locator(".generator-bookmark-load").click();
  await page.waitForFunction(() => /bookmarked composition loaded/i.test(
    document.getElementById("generatorActionStatus")?.textContent || ""
  ));
  assert.deepEqual(await getCompositionSnapshot(page), savedComposition);
  assert.deepEqual(await getControlSnapshot(page), savedControls);
  assert.equal(await page.locator("#generatorEmptyState").isHidden(), true);
  assert.equal(await page.locator(".generator-bookmark-load").getAttribute("aria-current"), "true");

  await page.reload({ waitUntil: "domcontentloaded" });
  await waitForGeneration(page, 24);
  await waitForBookmarkCount(page, 1);
  assert.equal(await page.locator("#generatorBackupBookmarksButton").isDisabled(), false);
  assert.deepEqual(await getCompositionSnapshot(page), savedComposition);
  assert.deepEqual(await getControlSnapshot(page), savedControls);
  assert.equal(await page.locator(".generator-bookmark-load").getAttribute("aria-current"), "true");

  await setRange(page, "#generatorCountSlider", 19);
  await setRange(page, "#generatorSizeSlider", 101);
  await page.locator("#generatorCategoryTab").click();
  const pendingControls = await getControlSnapshot(page);
  await waitForGeneration(page, 19);
  const dynamicallyUpdatedComposition = await getCompositionSnapshot(page);
  const activeSession = await readActiveSession(page);
  assert.equal(activeSession?.recordType, "active-session");
  assert.equal(activeSession?.composition?.specs?.length, 19);
  assert.equal(activeSession?.controls?.ranges?.generatorCountSlider, "19");
  assert.ok(activeSession?.history?.length > 0 && activeSession.history.length <= 30);

  await page.reload({ waitUntil: "domcontentloaded" });
  await waitForGeneration(page, 19);
  await waitForBookmarkCount(page, 1);
  assert.deepEqual(await getCompositionSnapshot(page), dynamicallyUpdatedComposition);
  assert.deepEqual(await getControlSnapshot(page), pendingControls);

  await page.locator("#generatorBookmarkGalleryModeButton").click();
  await page.locator(".generator-bookmark-details").evaluate((details) => {
    details.open = true;
  });
  await page.locator(".generator-bookmark-load").click();
  await page.waitForFunction(() => /bookmarked composition loaded/i.test(
    document.getElementById("generatorActionStatus")?.textContent || ""
  ));
  assert.deepEqual(await getCompositionSnapshot(page), savedComposition);
  assert.deepEqual(await getControlSnapshot(page), savedControls);

  await page.locator("#generatorUndoButton").click();
  await waitForGeneration(page, 19);
  assert.deepEqual(await getCompositionSnapshot(page), dynamicallyUpdatedComposition);
  assert.deepEqual(await getControlSnapshot(page), pendingControls);

  page.once("dialog", (dialog) => void dialog.accept());
  await page.locator(".generator-bookmark-delete").click();
  await waitForBookmarkCount(page, 0);
  assert.equal((await readBookmarkRecords(page)).length, 0);
  assert.equal(await page.locator("#generatorBookmarkButton").getAttribute("aria-pressed"), "false");

  await page.locator("#generatorRestoreBookmarksInput").setInputFiles(bookmarkBackupPath);
  await waitForBookmarkCount(page, 1);
  await page.waitForFunction(() => /bookmarks restored from backup/i.test(
    document.getElementById("generatorActionStatus")?.textContent || ""
  ));
  assert.equal((await readBookmarkRecords(page)).length, 1);
  await page.locator(".generator-bookmark-load").click();
  await page.waitForFunction(() => /bookmarked composition loaded/i.test(
    document.getElementById("generatorActionStatus")?.textContent || ""
  ));
  assert.deepEqual(await getCompositionSnapshot(page), savedComposition);
  assert.deepEqual(await getControlSnapshot(page), savedControls);

  page.once("dialog", (dialog) => void dialog.accept());
  await page.locator(".generator-bookmark-delete").click();
  await waitForBookmarkCount(page, 0);
  assert.deepEqual(errors, []);

  process.stdout.write("generator bookmark regression checks passed (save, reload, exact restore, backup, import, thumbnail, delete)\n");
} finally {
  await context.close();
  await browser.close();
  await new Promise((resolveClose) => localServer.server.close(resolveClose));
}
