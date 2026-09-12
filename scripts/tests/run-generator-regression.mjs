#!/usr/bin/env node

import assert from "node:assert/strict";
import { createReadStream, existsSync, statSync } from "node:fs";
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
  [".png", "image/png"]
]);

function createStaticServer(rootDirectory) {
  const server = createServer((request, response) => {
    let pathname;
    try {
      pathname = decodeURIComponent(new URL(request.url || "/", "http://127.0.0.1").pathname);
    } catch (error) {
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

async function setRange(page, selector, value) {
  await page.locator(selector).evaluate((input, nextValue) => {
    input.value = String(nextValue);
    input.dispatchEvent(new Event("input", { bubbles: true }));
  }, value);
}

const RANDOM_RANGE_SELECTORS = {
  size: ["#generatorSizeRandomMinSlider", "#generatorSizeRandomMaxSlider"],
  spacing: ["#generatorSpacingRandomMinSlider", "#generatorSpacingRandomMaxSlider"],
  rotation: ["#generatorRotationRandomMinSlider", "#generatorRotationRandomMaxSlider"],
  opacity: ["#generatorOpacityRandomMinSlider", "#generatorOpacityRandomMaxSlider"],
  tint: ["#generatorTintAmountRandomMinSlider", "#generatorTintAmountRandomMaxSlider"],
  spraySpread: ["#generatorSpraySpreadRandomMinSlider", "#generatorSpraySpreadRandomMaxSlider"],
  lineAngle: ["#generatorLineAngleRandomMinSlider", "#generatorLineAngleRandomMaxSlider"],
  lineLength: ["#generatorLineLengthRandomMinSlider", "#generatorLineLengthRandomMaxSlider"],
  boxWidth: ["#generatorBoxWidthRandomMinSlider", "#generatorBoxWidthRandomMaxSlider"],
  boxHeight: ["#generatorBoxHeightRandomMinSlider", "#generatorBoxHeightRandomMaxSlider"],
  sequenceSpeed: ["#generatorSequenceSpeedMinSlider", "#generatorSequenceSpeedSlider"],
  sequenceIntensity: ["#generatorSequenceIntensityMinSlider", "#generatorSequenceIntensitySlider"]
};

async function setRandomRange(page, key, minimum, maximum) {
  const selectors = RANDOM_RANGE_SELECTORS[key];
  assert.ok(selectors, `missing random range selectors for ${key}`);
  await page.evaluate(
    ({ minimumSelector, maximumSelector, nextMinimum, nextMaximum }) => {
      const minimumInput = document.querySelector(minimumSelector);
      const maximumInput = document.querySelector(maximumSelector);
      if (!(minimumInput instanceof HTMLInputElement) || !(maximumInput instanceof HTMLInputElement)) {
        throw new Error(`Could not find range inputs for ${minimumSelector}`);
      }
      minimumInput.value = String(nextMinimum);
      maximumInput.value = String(nextMaximum);
      minimumInput.dispatchEvent(new Event("input", { bubbles: true }));
      maximumInput.dispatchEvent(new Event("input", { bubbles: true }));
    },
    {
      minimumSelector: selectors[0],
      maximumSelector: selectors[1],
      nextMinimum: minimum,
      nextMaximum: maximum
    }
  );
}

function assertValuesWithin(values, minimum, maximum, label) {
  assert.ok(values.length > 0, `expected sampled ${label} values`);
  for (const value of values) {
    assert.ok(
      value >= minimum - 0.001 && value <= maximum + 0.001,
      `${label} ${value} should be inside ${minimum}–${maximum}`
    );
  }
}

async function setSourceSelection(page, kind, selectedValues) {
  await page.locator(`.generator-source-checkbox[data-source-kind="${kind}"]`).evaluateAll(
    (inputs, values) => {
      const selected = new Set(values);
      for (const input of inputs) {
        input.checked = selected.has(input.value);
      }
      inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
    },
    selectedValues
  );
}

async function setPlacementModes(page, selectedModes) {
  await page.locator(".generator-mode-checkbox").evaluateAll((inputs, values) => {
    const selected = new Set(values);
    for (const input of inputs) {
      input.checked = selected.has(input.value);
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  }, selectedModes);
}

async function generateWithSeed(page, seed, count) {
  await page.waitForFunction(() => {
    const button = document.getElementById("generatorGenerateButton");
    const canvas = document.getElementById("generatorCanvas");
    return Boolean(button && !button.disabled && canvas?.getAttribute("aria-busy") === "false");
  }, null, { timeout: 20000 });
  const generated = await page.evaluate(
    (nextSeed) => window.GeneratorApp.generate(nextSeed),
    seed
  );
  if (generated !== true) {
    const diagnostic = await page.evaluate(() => ({
      status: document.getElementById("generatorStatus")?.textContent,
      busy: document.getElementById("generatorCanvas")?.getAttribute("aria-busy"),
      generateDisabled: document.getElementById("generatorGenerateButton")?.disabled,
      effects: Array.from(document.querySelectorAll(".generator-sequence-effect-checkbox:checked"))
        .map((input) => input.value),
      timings: Array.from(document.querySelectorAll(".generator-sequence-timing-checkbox:checked"))
        .map((input) => input.value)
    }));
    assert.fail(`generation failed: ${JSON.stringify(diagnostic)}`);
  }
  const generatedState = await page.evaluate(() => ({
    count: document.querySelectorAll(".generator-stamp").length,
    summaryCount: window.GeneratorApp.getSummary().count,
    configuredCount: Number(document.getElementById("generatorCountSlider")?.value),
    countRandomized: Boolean(document.getElementById("generatorCountRandomToggle")?.checked),
    busy: document.getElementById("generatorCanvas")?.getAttribute("aria-busy")
  }));
  assert.equal(
    generatedState.count,
    count,
    `unexpected generated count: ${JSON.stringify(generatedState)}`
  );
  await waitForGeneration(page, count);
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

async function getCompositionSnapshot(page) {
  return page.evaluate(() => {
    const stamps = Array.from(document.querySelectorAll(".generator-stamp"));
    const sequenceStamps = stamps.filter((stamp) => stamp.classList.contains("has-generator-sequence"));
    const canvas = document.getElementById("generatorCanvas");
    const overlay = document.getElementById("generatorMarginOverlay");
    const coordinateWidth = Number.parseFloat(
      document.getElementById("generatorComposition")?.style.width || "0"
    );
    const coordinateHeight = Number.parseFloat(
      document.getElementById("generatorComposition")?.style.height || "0"
    );
    const sources = stamps.map((stamp) => stamp.dataset.generatorSource || "");
    const margin = Number(canvas?.dataset.generatorMargin || 0);
    const marginMode = canvas?.dataset.generatorMarginMode || "";
    const modes = Object.fromEntries(
      ["line", "spray", "box", "scatter"].map((mode) => [
        mode,
        stamps.filter((stamp) => stamp.dataset.generatorMode === mode).length
      ])
    );
    return {
      count: stamps.length,
      uniqueSourceCount: new Set(sources).size,
      categories: Array.from(new Set(stamps.map((stamp) => stamp.dataset.generatorCategory))),
      tagFilterViolations: stamps.filter((stamp) => {
        const selectedTags = Array.from(
          document.querySelectorAll('.generator-source-checkbox[data-source-kind="tag"]:checked')
        ).map((input) => input.value);
        if (!selectedTags.length) {
          return false;
        }
        const stampTags = String(stamp.dataset.generatorTags || "").split(",");
        return !selectedTags.some((tag) => stampTags.includes(tag));
      }).length,
      modes,
      coordinateWidth,
      coordinateHeight,
      margin,
      marginMode,
      marginViolations: stamps.filter((stamp) => {
        if (marginMode !== "placement" || margin <= 0) {
          return false;
        }
        const x = Number(stamp.dataset.generatorX);
        const y = Number(stamp.dataset.generatorY);
        const width = Number.parseFloat(stamp.style.width);
        const height = Number.parseFloat(stamp.style.height);
        const rotation = Number(stamp.dataset.generatorRotation) * Math.PI / 180;
        const halfExtentX = (Math.abs(Math.cos(rotation)) * width + Math.abs(Math.sin(rotation)) * height) / 2;
        const halfExtentY = (Math.abs(Math.sin(rotation)) * width + Math.abs(Math.cos(rotation)) * height) / 2;
        const tolerance = 0.02;
        return x - halfExtentX < margin - tolerance ||
          x + halfExtentX > coordinateWidth - margin + tolerance ||
          y - halfExtentY < margin - tolerance ||
          y + halfExtentY > coordinateHeight - margin + tolerance;
      }).length,
      croppedCenterCount: stamps.filter((stamp) => {
        const x = Number(stamp.dataset.generatorX);
        const y = Number(stamp.dataset.generatorY);
        return x < margin || x > coordinateWidth - margin || y < margin || y > coordinateHeight - margin;
      }).length,
      overlay: {
        hidden: Boolean(overlay?.hidden),
        borderWidth: overlay?.style.borderWidth || "",
        borderColor: overlay ? getComputedStyle(overlay).borderTopColor : "",
        pointerEvents: overlay ? getComputedStyle(overlay).pointerEvents : "",
        zIndex: overlay ? Number(getComputedStyle(overlay).zIndex) : 0,
        parentId: overlay?.parentElement?.id || ""
      },
      canvasBackground: canvas?.style.backgroundColor || "",
      sourceIndexSignature: stamps
        .slice()
        .sort((left, right) => Number(left.dataset.generatorIndex) - Number(right.dataset.generatorIndex))
        .map((stamp) => stamp.dataset.generatorSource || "")
        .join("|"),
      canvasAriaLabel: canvas?.getAttribute("aria-label") || "",
      maximumStampZIndex: Math.max(0, ...stamps.map((stamp) => Number(stamp.style.zIndex) || 0)),
      outOfBounds: stamps.filter((stamp) => {
        const x = Number(stamp.dataset.generatorX);
        const y = Number(stamp.dataset.generatorY);
        return x < 0 || y < 0 || x > coordinateWidth || y > coordinateHeight;
      }).length,
      wrongAssetBase: stamps.filter((stamp) =>
        new URL(stamp.src).pathname.includes("/generator/brushes/")
      ).length,
      sizes: Array.from(new Set(stamps.map((stamp) => stamp.dataset.generatorSize))),
      rotations: Array.from(new Set(stamps.map((stamp) => stamp.dataset.generatorRotation))),
      opacities: Array.from(new Set(stamps.map((stamp) => stamp.dataset.generatorOpacity))),
      sizeValues: stamps.map((stamp) => Number(stamp.dataset.generatorSize)),
      rotationValues: stamps.map((stamp) => Number(stamp.dataset.generatorRotation)),
      opacityValues: stamps.map((stamp) => Number(stamp.dataset.generatorOpacity)),
      tintValues: stamps.map((stamp) => Number(stamp.dataset.generatorTintAmount)),
      sampledGeometry: Object.fromEntries([
        "sampledSpacing",
        "sampledLineLength",
        "sampledLineAngle",
        "sampledSpraySpread",
        "sampledBoxWidth",
        "sampledBoxHeight"
      ].map((key) => [
        key,
        stamps.map((stamp) => Number(stamp.dataset[key])).filter(Number.isFinite)
      ])),
      sequenceSpeedValues: sequenceStamps
        .map((stamp) => Number(stamp.dataset.generatorSequenceSpeed))
        .filter(Number.isFinite),
      sequenceIntensityValues: sequenceStamps
        .map((stamp) => Number(stamp.dataset.generatorSequenceIntensity))
        .filter(Number.isFinite),
      sequenceCount: sequenceStamps.length,
      sequenceLayerCount: new Set(sequenceStamps.map(
        (stamp) => stamp.dataset.generatorMotif
      )).size,
      sequenceEffects: Array.from(new Set(sequenceStamps.map(
        (stamp) => stamp.dataset.generatorSequenceEffect
      ))).sort(),
      sequenceTimings: Array.from(new Set(sequenceStamps.map(
        (stamp) => stamp.dataset.generatorSequenceTiming
      ))).sort(),
      sequenceAssignments: sequenceStamps
        .slice()
        .sort((left, right) => Number(left.dataset.generatorIndex) - Number(right.dataset.generatorIndex))
        .map((stamp) => ({
          index: Number(stamp.dataset.generatorIndex),
          effect: stamp.dataset.generatorSequenceEffect || "",
          timing: stamp.dataset.generatorSequenceTiming || "",
          speed: Number(stamp.dataset.generatorSequenceSpeed),
          intensity: Number(stamp.dataset.generatorSequenceIntensity),
          duration: stamp.style.getPropertyValue("--generator-sequence-duration"),
          delay: stamp.style.getPropertyValue("--generator-sequence-delay")
        })),
      sequenceSignature: sequenceStamps.map((stamp) => [
        stamp.dataset.generatorMotif,
        stamp.dataset.generatorSequenceEffect,
        stamp.dataset.generatorSequenceTiming,
        stamp.style.getPropertyValue("--generator-sequence-duration"),
        stamp.style.getPropertyValue("--generator-sequence-delay"),
        stamp.style.getPropertyValue("--generator-sequence-move-x"),
        stamp.style.getPropertyValue("--generator-sequence-move-y"),
        stamp.dataset.generatorSequenceAlternateSource || ""
      ].join("|")).join(";"),
      signature: stamps.slice(0, 24).map((stamp) => [
        stamp.dataset.generatorSource,
        stamp.dataset.generatorX,
        stamp.dataset.generatorY,
        stamp.dataset.generatorSize,
        stamp.dataset.generatorRotation,
        stamp.dataset.generatorMode
      ].join("|")).join(";"),
      nonSequenceVisualSignature: stamps.map((stamp) => [
        stamp.dataset.generatorIndex,
        stamp.dataset.generatorSource,
        stamp.dataset.generatorX,
        stamp.dataset.generatorY,
        stamp.dataset.generatorSize,
        stamp.dataset.generatorRotation,
        stamp.dataset.generatorOpacity,
        stamp.dataset.generatorTintAmount,
        stamp.dataset.sampledSpacing || "",
        stamp.dataset.sampledLineLength || "",
        stamp.dataset.sampledLineAngle || "",
        stamp.dataset.sampledSpraySpread || "",
        stamp.dataset.sampledBoxWidth || "",
        stamp.dataset.sampledBoxHeight || "",
        stamp.dataset.generatorMode
      ].join("|")).join(";"),
      visualSignature: stamps.map((stamp) => [
        stamp.dataset.generatorSource,
        stamp.dataset.generatorX,
        stamp.dataset.generatorY,
        stamp.dataset.generatorSize,
        stamp.dataset.generatorRotation,
        stamp.dataset.generatorOpacity,
        stamp.dataset.generatorTintAmount,
        stamp.dataset.sampledSpacing || "",
        stamp.dataset.sampledLineLength || "",
        stamp.dataset.sampledLineAngle || "",
        stamp.dataset.sampledSpraySpread || "",
        stamp.dataset.sampledBoxWidth || "",
        stamp.dataset.sampledBoxHeight || "",
        stamp.dataset.generatorSequenceSpeed || "",
        stamp.dataset.generatorSequenceIntensity || "",
        stamp.dataset.generatorMode
      ].join("|")).join(";")
    };
  });
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

  const categoryChoices = page.locator(
    '.generator-source-checkbox[data-source-kind="category"]'
  );
  const tagChoices = page.locator('.generator-source-checkbox[data-source-kind="tag"]');
  assert.equal(await categoryChoices.count(), 15);
  assert.equal(await page.locator(
    '.generator-source-checkbox[data-source-kind="category"]:checked'
  ).count(), 15);
  assert.equal(await tagChoices.count(), 23);
  assert.equal(await page.locator(
    '.generator-source-checkbox[data-source-kind="tag"]:checked'
  ).count(), 23);
  assert.equal(await page.locator("#generatorCatalogCount").textContent(), "3,070 gifs");
  assert.equal(await page.locator("#generatorCategorySelectionCount").textContent(), "15 selected");
  assert.equal(await page.locator("#generatorTagSelectionCount").textContent(), "23 selected");
  assert.equal(await page.locator("#generatorCategoryTab").getAttribute("aria-selected"), "true");
  assert.equal(await page.locator("#generatorCategoryTab").getAttribute("tabindex"), "0");
  assert.equal(await page.locator("#generatorTagTab").getAttribute("aria-selected"), "false");
  assert.equal(await page.locator("#generatorTagTab").getAttribute("tabindex"), "-1");
  assert.equal(await page.locator("#generatorCategoryPanel").isHidden(), false);
  assert.equal(await page.locator("#generatorTagPanel").isHidden(), true);
  assert.equal(await page.locator("#generatorCountSlider").getAttribute("min"), "1");
  assert.equal(await page.locator("#generatorCountSlider").getAttribute("max"), "300");
  assert.equal(await page.locator("#generatorAspectLockButton").count(), 0);
  assert.equal(await page.locator("#generatorExportCancelButton").isHidden(), true);
  assert.equal(await page.locator(
    "#generatorMarginRandomToggle, #generatorMarginModeRandomToggle, #generatorCountRandomToggle, #generatorSequenceEffectsRandomToggle"
  ).count(), 4);
  assert.equal(await page.locator(
    "#generatorMarginRandomToggle:checked, #generatorMarginModeRandomToggle:checked, #generatorCountRandomToggle:checked, #generatorSequenceEffectsRandomToggle:checked"
  ).count(), 0);
  assert.equal(await page.locator(".generator-range-random-checkbox").count(), 12);
  assert.equal(await page.locator(".generator-range-random-checkbox:checked").count(), 0);

  const expandedRangeDomains = await page.evaluate(() => Object.fromEntries([
    ["size", "generatorSizeSlider", "generatorSizeRandomMinSlider", "generatorSizeRandomMaxSlider"],
    ["spacing", "generatorSpacingSlider", "generatorSpacingRandomMinSlider", "generatorSpacingRandomMaxSlider"],
    ["rotation", "generatorRotationSlider", "generatorRotationRandomMinSlider", "generatorRotationRandomMaxSlider"],
    ["opacity", "generatorOpacitySlider", "generatorOpacityRandomMinSlider", "generatorOpacityRandomMaxSlider"],
    ["tint", "generatorTintAmountSlider", "generatorTintAmountRandomMinSlider", "generatorTintAmountRandomMaxSlider"],
    ["spraySpread", "generatorSpraySpreadSlider", "generatorSpraySpreadRandomMinSlider", "generatorSpraySpreadRandomMaxSlider"],
    ["lineAngle", "generatorLineAngleSlider", "generatorLineAngleRandomMinSlider", "generatorLineAngleRandomMaxSlider"],
    ["lineLength", "generatorLineLengthSlider", "generatorLineLengthRandomMinSlider", "generatorLineLengthRandomMaxSlider"],
    ["boxWidth", "generatorBoxWidthSlider", "generatorBoxWidthRandomMinSlider", "generatorBoxWidthRandomMaxSlider"],
    ["boxHeight", "generatorBoxHeightSlider", "generatorBoxHeightRandomMinSlider", "generatorBoxHeightRandomMaxSlider"],
    ["sequenceSpeed", null, "generatorSequenceSpeedMinSlider", "generatorSequenceSpeedSlider"],
    ["sequenceIntensity", null, "generatorSequenceIntensityMinSlider", "generatorSequenceIntensitySlider"]
  ].map(([key, fixedId, minimumId, maximumId]) => {
    const ids = [fixedId, minimumId, maximumId].filter(Boolean);
    return [key, ids.map((id) => {
      const input = document.getElementById(id);
      return {
        id,
        min: Number(input?.min),
        max: Number(input?.max),
        step: Number(input?.step)
      };
    })];
  })));
  const expectedDomains = {
    size: [8, 2400],
    spacing: [4, 2000],
    rotation: [-180, 180],
    opacity: [1, 100],
    tint: [0, 100],
    spraySpread: [8, 2400],
    lineAngle: [-180, 180],
    lineLength: [8, 4000],
    boxWidth: [8, 2400],
    boxHeight: [8, 2400],
    sequenceSpeed: [1, 100],
    sequenceIntensity: [0, 300]
  };
  for (const [key, inputs] of Object.entries(expandedRangeDomains)) {
    assert.ok(inputs.length >= 2, `expected dual range inputs for ${key}`);
    for (const input of inputs) {
      assert.deepEqual(
        [input.min, input.max, input.step],
        [...expectedDomains[key], 1],
        `unexpected domain for ${input.id}`
      );
    }
  }
  assert.equal(await page.locator("#generatorSizeSlider").isDisabled(), true);
  assert.equal(await page.locator("#generatorSizeRandomMinSlider").isEnabled(), true);
  assert.equal(await page.locator("#generatorSizeRandomMaxSlider").isEnabled(), true);

  await setRange(page, "#generatorSizeRandomMaxSlider", 900);
  await setRange(page, "#generatorSizeRandomMinSlider", 800);
  await setRange(page, "#generatorSizeRandomMaxSlider", 700);
  assert.deepEqual(
    await page.locator(
      "#generatorSizeRandomMinSlider, #generatorSizeRandomMaxSlider"
    ).evaluateAll((inputs) => inputs.map((input) => input.value)),
    ["800", "800"]
  );
  assert.equal(await page.locator('[data-random-range="size"]').getAttribute("data-range-minimum"), "800");
  assert.equal(await page.locator('[data-random-range="size"]').getAttribute("data-range-maximum"), "800");
  assert.equal(await page.locator("#generatorSizeValue").textContent(), "800–800px");
  const sizeRangeWrapper = page.locator('[data-random-range="size"]');
  await sizeRangeWrapper.scrollIntoViewIfNeeded();
  const sizeRangeBox = await sizeRangeWrapper.boundingBox();
  assert.ok(sizeRangeBox, "expected a visible dual-range track");
  await page.mouse.click(
    sizeRangeBox.x + sizeRangeBox.width * 0.2,
    sizeRangeBox.y + sizeRangeBox.height / 2
  );
  assert.ok(Number(await page.locator("#generatorSizeRandomMinSlider").inputValue()) < 800);
  assert.equal(await page.locator("#generatorSizeRandomMaxSlider").inputValue(), "800");
  await setRandomRange(page, "size", 46, 158);

  await setRandomRange(page, "sequenceIntensity", 220, 250);
  await setRange(page, "#generatorSequenceIntensitySlider", 150);
  assert.deepEqual(
    await page.locator(
      "#generatorSequenceIntensityMinSlider, #generatorSequenceIntensitySlider"
    ).evaluateAll((inputs) => inputs.map((input) => input.value)),
    ["220", "220"]
  );
  assert.equal(await page.locator("#generatorSequenceIntensityValue").textContent(), "220–220%");
  await setRandomRange(page, "sequenceIntensity", 47, 78);
  await generateWithSeed(page, 0xdeadbeef, 120);

  const defaultSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.equal(defaultSummary.catalogSize, 3070);
  assert.equal(defaultSummary.activePoolSize, 3070);
  assert.equal(defaultSummary.sourceMode, "category");
  assert.equal(defaultSummary.selectedCategories.length, 15);
  assert.equal(defaultSummary.selectedTags.length, 23);

  const initial = await getCompositionSnapshot(page);
  assert.equal(initial.count, 120);
  assert.equal(initial.uniqueSourceCount, 120);
  assert.equal(initial.outOfBounds, 0);
  assert.equal(initial.wrongAssetBase, 0);
  assert.equal(initial.margin, 0);
  assert.equal(initial.marginMode, "placement");
  assert.equal(initial.overlay.hidden, true);
  for (const mode of ["line", "spray", "box", "scatter"]) {
    assert.ok(initial.modes[mode] > 0, `expected ${mode} placements`);
  }
  assert.equal(initial.sequenceCount, 120);
  assert.ok(initial.sequenceLayerCount > 1);
  assert.ok(initial.sequenceEffects.length > 1);
  assert.ok(initial.sequenceTimings.length > 1);
  assert.equal(defaultSummary.sequenceEnabled, true);
  assert.equal(defaultSummary.sequenceLayerCount, initial.sequenceLayerCount);
  assert.deepEqual(
    Object.keys(defaultSummary.sequenceEffectCounts).sort(),
    initial.sequenceEffects
  );
  assert.deepEqual(
    Object.keys(defaultSummary.sequenceTimingCounts).sort(),
    initial.sequenceTimings
  );

  await generateWithSeed(page, 0xdeadbeef, 120);
  const deterministic = await getCompositionSnapshot(page);
  assert.equal(deterministic.signature, initial.signature);
  assert.equal(deterministic.sequenceSignature, initial.sequenceSignature);

  await page.locator(
    "#generatorMarginRandomToggle, #generatorMarginModeRandomToggle, #generatorCountRandomToggle, #generatorSequenceEffectsRandomToggle"
  ).evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = true;
      input.dispatchEvent(new Event("change", { bubbles: true }));
    }
  });
  await page.locator("#generatorSizeRangeRandomToggle").check({ force: true });
  await page.locator("#generatorSequenceSpeedRangeRandomToggle").check({ force: true });
  const stableOpacityRange = await page.locator(
    "#generatorOpacityRandomMinSlider, #generatorOpacityRandomMaxSlider"
  ).evaluateAll((inputs) => inputs.map((input) => input.value));
  assert.equal(await page.evaluate(() => window.GeneratorApp.generate(0x13579bdf)), true);
  const randomizedGeneration = await page.evaluate(() => ({
    summary: window.GeneratorApp.getSummary(),
    controls: {
      count: Number(document.getElementById("generatorCountSlider")?.value),
      margin: Number(document.getElementById("generatorMarginSlider")?.value),
      marginMaximum: Number(document.getElementById("generatorMarginSlider")?.max),
      marginMode: document.querySelector('input[name="generatorMarginMode"]:checked')?.value,
      effects: Array.from(document.querySelectorAll(".generator-sequence-effect-checkbox:checked"))
        .map((input) => input.value),
      sizeRange: [
        Number(document.getElementById("generatorSizeRandomMinSlider")?.value),
        Number(document.getElementById("generatorSizeRandomMaxSlider")?.value)
      ],
      sequenceSpeedRange: [
        Number(document.getElementById("generatorSequenceSpeedMinSlider")?.value),
        Number(document.getElementById("generatorSequenceSpeedSlider")?.value)
      ]
    }
  }));
  assert.ok(randomizedGeneration.controls.count >= 1 && randomizedGeneration.controls.count <= 300);
  assert.equal(randomizedGeneration.summary.count, randomizedGeneration.controls.count);
  assert.ok(randomizedGeneration.controls.margin >= 0);
  assert.ok(randomizedGeneration.controls.margin <= randomizedGeneration.controls.marginMaximum);
  assert.equal(randomizedGeneration.summary.margin, randomizedGeneration.controls.margin);
  assert.equal(randomizedGeneration.summary.marginMode, randomizedGeneration.controls.marginMode);
  assert.ok(randomizedGeneration.controls.effects.length > 0);
  assert.ok(randomizedGeneration.controls.effects.length < 8);
  assert.notDeepEqual(randomizedGeneration.controls.sizeRange, [46, 158]);
  assert.notDeepEqual(randomizedGeneration.controls.sequenceSpeedRange, [52, 78]);
  assert.deepEqual(
    await page.locator(
      "#generatorOpacityRandomMinSlider, #generatorOpacityRandomMaxSlider"
    ).evaluateAll((inputs) => inputs.map((input) => input.value)),
    stableOpacityRange
  );
  assert.deepEqual(randomizedGeneration.summary.generationRandomize, {
    margin: true,
    marginMode: true,
    count: true,
    sequenceEffects: true
  });
  assert.equal(randomizedGeneration.summary.rangeRandomize.size, true);
  assert.equal(randomizedGeneration.summary.rangeRandomize.sequenceSpeed, true);
  assert.equal(
    Object.values(randomizedGeneration.summary.rangeRandomize).filter(Boolean).length,
    2
  );

  assert.equal(await page.evaluate(() => window.GeneratorApp.generate(0x13579bdf)), true);
  const repeatedRandomizedGeneration = await page.evaluate(() => ({
    summary: window.GeneratorApp.getSummary(),
    effects: Array.from(document.querySelectorAll(".generator-sequence-effect-checkbox:checked"))
      .map((input) => input.value),
    sizeRange: [
      Number(document.getElementById("generatorSizeRandomMinSlider")?.value),
      Number(document.getElementById("generatorSizeRandomMaxSlider")?.value)
    ],
    sequenceSpeedRange: [
      Number(document.getElementById("generatorSequenceSpeedMinSlider")?.value),
      Number(document.getElementById("generatorSequenceSpeedSlider")?.value)
    ]
  }));
  assert.equal(repeatedRandomizedGeneration.summary.signature, randomizedGeneration.summary.signature);
  assert.equal(repeatedRandomizedGeneration.summary.count, randomizedGeneration.summary.count);
  assert.equal(repeatedRandomizedGeneration.summary.margin, randomizedGeneration.summary.margin);
  assert.equal(repeatedRandomizedGeneration.summary.marginMode, randomizedGeneration.summary.marginMode);
  assert.deepEqual(repeatedRandomizedGeneration.effects, randomizedGeneration.controls.effects);
  assert.deepEqual(repeatedRandomizedGeneration.sizeRange, randomizedGeneration.controls.sizeRange);
  assert.deepEqual(
    repeatedRandomizedGeneration.sequenceSpeedRange,
    randomizedGeneration.controls.sequenceSpeedRange
  );

  await page.locator(
    "#generatorMarginRandomToggle, #generatorMarginModeRandomToggle, #generatorCountRandomToggle, #generatorSequenceEffectsRandomToggle, #generatorSizeRangeRandomToggle, #generatorSequenceSpeedRangeRandomToggle"
  ).evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = false;
      input.dispatchEvent(new Event("change", { bubbles: true }));
    }
  });
  await page.waitForTimeout(250);
  await page.waitForFunction(
    () => document.getElementById("generatorCanvas")?.getAttribute("aria-busy") === "false"
  );
  await page.locator(".generator-sequence-effect-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = true;
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.locator('.generator-margin-mode-choice:has(input[value="placement"]) span').click();
  await setRange(page, "#generatorCountSlider", 120);
  await setRange(page, "#generatorMarginSlider", 0);
  await setRandomRange(page, "size", 46, 158);
  await setRandomRange(page, "sequenceSpeed", 52, 78);
  await generateWithSeed(page, 0xdeadbeef, 120);

  await page.locator("#generatorSequencePauseButton").click();
  assert.equal(await page.locator("#generatorSequencePauseButton").getAttribute("aria-pressed"), "true");
  assert.equal(
    await page.locator(".generator-stamp.has-generator-sequence").first().evaluate(
      (stamp) => getComputedStyle(stamp).animationPlayState
    ),
    "paused"
  );
  await page.locator("#generatorSequencePauseButton").click();
  assert.equal(await page.locator("#generatorSequencePauseButton").getAttribute("aria-pressed"), "false");

  await page.emulateMedia({ reducedMotion: "reduce" });
  assert.equal(
    await page.locator(".generator-stamp.has-generator-sequence").first().evaluate(
      (stamp) => getComputedStyle(stamp).animationName
    ),
    "none"
  );
  await page.emulateMedia({ reducedMotion: "no-preference" });
  assert.notEqual(
    await page.locator(".generator-stamp.has-generator-sequence").first().evaluate(
      (stamp) => getComputedStyle(stamp).animationName
    ),
    "none"
  );

  await page.locator(".generator-sequence-effect-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = input.value === "pixelate";
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.locator(".generator-sequence-timing-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = input.value === "all";
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await setRange(page, "#generatorCountSlider", 12);
  await generateWithSeed(page, 0xabcdef01, 12);
  await page.waitForFunction(
    () => Boolean(document.querySelector(".generator-pixelate-proxy:not([hidden])")),
    null,
    { timeout: 15000 }
  );
  const pixelateParity = await page.locator(
    ".generator-pixelate-proxy:not([hidden])"
  ).first().evaluate((proxy) => {
    const image = document.querySelector(
      `.generator-stamp[data-generator-index="${proxy.dataset.generatorIndex}"]`
    );
    const blockSize = Number(proxy.dataset.generatorPixelateBlockSize);
    const scale = Number(proxy.dataset.generatorPixelateScale);
    const width = Number.parseFloat(image.style.width);
    const height = Number.parseFloat(image.style.height);
    return {
      baseAmount: Number(image.dataset.generatorPixelateAmount),
      blockSize,
      expectedBaseAmount: Math.round(
        2 + Number(image.dataset.generatorSequenceIntensity) / 100 * 14
      ),
      expectedPixelWidth: Math.ceil(width * scale / blockSize),
      expectedPixelHeight: Math.ceil(height * scale / blockSize),
      pixelWidth: proxy.width,
      pixelHeight: proxy.height,
      imageVisibility: getComputedStyle(image).visibility,
      proxyImageRendering: getComputedStyle(proxy).imageRendering
    };
  });
  assert.equal(pixelateParity.baseAmount, pixelateParity.expectedBaseAmount);
  assert.ok(pixelateParity.blockSize > 1);
  assert.ok(pixelateParity.blockSize <= pixelateParity.baseAmount);
  assert.equal(pixelateParity.pixelWidth, pixelateParity.expectedPixelWidth);
  assert.equal(pixelateParity.pixelHeight, pixelateParity.expectedPixelHeight);
  assert.equal(pixelateParity.imageVisibility, "hidden");
  assert.equal(pixelateParity.proxyImageRendering, "pixelated");

  await page.locator(".generator-sequence-effect-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = true;
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.locator(".generator-sequence-timing-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = true;
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await setRange(page, "#generatorCountSlider", 120);
  await generateWithSeed(page, 0xdeadbeef, 120);

  await page.locator("#generatorCategoryTab").focus();
  await page.keyboard.press("End");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "generatorTagTab");
  assert.equal(await page.locator("#generatorTagTab").getAttribute("aria-selected"), "true");
  assert.equal(await page.locator("#generatorTagPanel").isHidden(), false);
  assert.equal(await page.locator("#generatorCategoryPanel").isHidden(), true);
  await page.keyboard.press("Home");
  assert.equal(await page.evaluate(() => document.activeElement?.id), "generatorCategoryTab");
  assert.equal(await page.locator("#generatorCategoryTab").getAttribute("aria-selected"), "true");

  await setSourceSelection(page, "category", ["radial", "flower"]);
  let sourceSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.equal(sourceSummary.sourceMode, "category");
  assert.deepEqual(sourceSummary.selectedCategories, ["radial", "flower"]);
  assert.equal(sourceSummary.selectedTags.length, 23);
  assert.equal(sourceSummary.activePoolSize, 151);
  assert.equal(await page.locator("#generatorCatalogCount").textContent(), "151 gifs");
  assert.equal(await page.locator("#generatorCountSlider").getAttribute("max"), "151");
  assert.match(await page.locator("#generatorSourceHint").textContent(), /2 categories enabled/i);
  await setRange(page, "#generatorCountSlider", 100);
  await generateWithSeed(page, 0x11112222, 100);
  const categoryUnion = await getCompositionSnapshot(page);
  assert.equal(categoryUnion.uniqueSourceCount, 100);
  assert.deepEqual(categoryUnion.categories.sort(), ["flower", "radial"]);

  await page.locator("#generatorTagTab").click();
  await setSourceSelection(page, "tag", ["live-action", "meme"]);
  sourceSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.equal(sourceSummary.sourceMode, "tag");
  assert.deepEqual(sourceSummary.selectedCategories, ["radial", "flower"]);
  assert.deepEqual(sourceSummary.selectedTags, ["live-action", "meme"]);
  assert.equal(sourceSummary.activePoolSize, 24);
  assert.equal(await page.locator("#generatorCatalogCount").textContent(), "24 gifs");
  assert.equal(await page.locator("#generatorCountSlider").getAttribute("max"), "24");
  assert.match(await page.locator("#generatorSourceHint").textContent(), /2 tags enabled/i);
  await setRange(page, "#generatorCountSlider", 24);
  await generateWithSeed(page, 0x33334444, 24);
  const tagUnion = await getCompositionSnapshot(page);
  assert.equal(tagUnion.uniqueSourceCount, 24);
  assert.equal(tagUnion.tagFilterViolations, 0);

  await setSourceSelection(page, "tag", ["meme"]);
  sourceSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.deepEqual(sourceSummary.selectedTags, ["meme"]);
  assert.equal(sourceSummary.activePoolSize, 2);
  assert.equal(await page.locator("#generatorCountSlider").getAttribute("min"), "1");
  assert.equal(await page.locator("#generatorCountSlider").getAttribute("max"), "2");
  assert.equal(await page.locator("#generatorCountSlider").inputValue(), "2");
  await generateWithSeed(page, 0x55556666, 2);
  const memeOnly = await getCompositionSnapshot(page);
  assert.equal(memeOnly.count, 2);
  assert.equal(memeOnly.uniqueSourceCount, 2);
  assert.equal(memeOnly.tagFilterViolations, 0);

  await page.locator("#generatorCategoryTab").click();
  sourceSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.deepEqual(sourceSummary.selectedCategories, ["radial", "flower"]);
  assert.deepEqual(sourceSummary.selectedTags, ["meme"]);
  assert.equal(sourceSummary.activePoolSize, 151);
  await page.locator("#generatorTagTab").click();
  assert.equal((await page.evaluate(() => window.GeneratorApp.getSummary())).activePoolSize, 2);

  const beforeEmptySource = await page.evaluate(() => window.GeneratorApp.getSummary());
  await setSourceSelection(page, "tag", []);
  sourceSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.equal(sourceSummary.activePoolSize, 0);
  assert.equal(await page.locator("#generatorCatalogCount").textContent(), "0 gifs");
  assert.equal(await page.locator("#generatorGenerateButton").isDisabled(), true);
  assert.match(await page.locator("#generatorSourceHint").textContent(), /select at least one tag/i);
  assert.match(await page.locator("#generatorStatus").textContent(), /select at least one tag/i);
  assert.equal(await page.evaluate(() => window.GeneratorApp.generate(0x77778888)), false);
  const afterEmptySource = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.equal(afterEmptySource.signature, beforeEmptySource.signature);
  assert.equal(afterEmptySource.count, beforeEmptySource.count);

  await page.locator('[data-source-kind="tag"][data-source-action="all"]').click();
  await page.locator("#generatorCategoryTab").click();
  await page.locator('[data-source-kind="category"][data-source-action="all"]').click();
  await page.locator("#generatorSequenceEnabledToggle").uncheck({ force: true });
  assert.equal(await page.locator("#generatorSequenceStateLabel").textContent(), "off");

  await setRange(page, "#generatorCountSlider", 37);
  await page.locator("#generatorGenerateButton").click();
  await waitForGeneration(page, 37);
  const regenerated = await getCompositionSnapshot(page);
  assert.equal(regenerated.count, 37);
  assert.equal(regenerated.uniqueSourceCount, 37);
  assert.notEqual(regenerated.signature, initial.signature);
  assert.equal(regenerated.sequenceCount, 0);
  assert.equal((await page.evaluate(() => window.GeneratorApp.getSummary())).sequenceEnabled, false);

  await page.locator("#generatorRandomizeAllToggle").uncheck({ force: true });
  await setPlacementModes(page, ["line"]);
  await setRange(page, "#generatorCountSlider", 31);
  await setRange(page, "#generatorSizeSlider", 72);
  await setRange(page, "#generatorRotationSlider", 15);
  await setRange(page, "#generatorOpacitySlider", 85);
  await setRange(page, "#generatorMarginSlider", 80);
  await page.locator("#generatorGenerateButton").click();
  await waitForGeneration(page, 31);
  const fixed = await getCompositionSnapshot(page);
  assert.deepEqual(Object.entries(fixed.modes).filter(([, count]) => count > 0), [["line", 31]]);
  assert.equal(fixed.uniqueSourceCount, 1);
  assert.deepEqual(fixed.sizes, ["72.000"]);
  assert.deepEqual(fixed.rotations, ["15.000"]);
  assert.deepEqual(fixed.opacities, ["0.8500"]);
  assert.equal(fixed.margin, 80);
  assert.equal(fixed.marginMode, "placement");
  assert.equal(fixed.marginViolations, 0);
  assert.equal(fixed.overlay.hidden, true);

  assert.equal(await page.locator("#generatorSizeSlider").isEnabled(), true);
  assert.equal(await page.locator("#generatorSizeRandomMinSlider").isDisabled(), true);
  assert.equal(await page.locator("#generatorSizeRandomMaxSlider").isDisabled(), true);

  await setPlacementModes(page, ["scatter"]);
  await setRange(page, "#generatorCountSlider", 1);
  await setRange(page, "#generatorMarginSlider", 0);
  await page.locator("#generatorBackgroundRandomToggle").check({ force: true });
  const backgroundSeeds = Array.from(
    { length: 64 },
    (_, index) => Math.imul(index + 1, 0x9e3779b1) >>> 0
  );
  const randomBackgrounds = await page.evaluate(async (seeds) => {
    const colors = [];
    for (const seed of seeds) {
      if (!await window.GeneratorApp.generate(seed)) {
        throw new Error(`Could not generate background sample ${seed}`);
      }
      colors.push(window.GeneratorApp.getSummary().backgroundColor);
    }
    return colors;
  }, backgroundSeeds);
  assert.ok(randomBackgrounds.every((color) => /^#[\da-f]{6}$/i.test(color)));
  assert.ok(new Set(randomBackgrounds).size >= 63, "expected full-gamut background diversity");
  const legacyBackgroundPalette = new Set([
    "#ffffff", "#f5f0e7", "#edf4f3", "#f1eef8", "#fbefef",
    "#eff3fb", "#f4f1d9", "#19191f", "#10262b"
  ]);
  assert.ok(
    randomBackgrounds.some((color) => !legacyBackgroundPalette.has(color)),
    "expected colors outside the former fixed palette"
  );
  const colorChannels = [0, 1, 2].map((channel) => randomBackgrounds.map((color) => {
    const packed = Number.parseInt(color.slice(1), 16);
    return (packed >>> ((2 - channel) * 8)) & 0xff;
  }));
  for (const channel of colorChannels) {
    assert.ok(Math.min(...channel) < 32, "expected randomized backgrounds near the low channel bound");
    assert.ok(Math.max(...channel) > 223, "expected randomized backgrounds near the high channel bound");
  }
  const repeatedBackgrounds = [];
  for (let attempt = 0; attempt < 2; attempt += 1) {
    await generateWithSeed(page, 0xdecafbad, 1);
    repeatedBackgrounds.push((await page.evaluate(() => window.GeneratorApp.getSummary())).backgroundColor);
  }
  assert.equal(repeatedBackgrounds[0], repeatedBackgrounds[1]);

  await page.locator("#generatorBackgroundRandomToggle").uncheck({ force: true });
  await page.locator("#generatorBackgroundColorInput").evaluate((input) => {
    input.value = "#123456";
    input.dispatchEvent(new Event("input", { bubbles: true }));
  });
  await generateWithSeed(page, 0xdecafbad, 1);
  assert.equal(
    (await page.evaluate(() => window.GeneratorApp.getSummary())).backgroundColor,
    "#123456"
  );
  assert.equal(
    await page.locator("#generatorCanvas").evaluate((canvas) => canvas.style.backgroundColor),
    "rgb(18, 52, 86)"
  );

  await page.locator("#generatorRandomizeAllToggle").check({ force: true });
  await page.locator("#generatorSequenceEnabledToggle").check({ force: true });
  await page.locator('[data-canvas-size="900x900"]').click();
  await setPlacementModes(page, ["line", "spray", "box", "scatter"]);
  await setRange(page, "#generatorCountSlider", 96);
  const visualRanges = {
    size: [300, 420],
    spacing: [90, 150],
    rotation: [-37, 41],
    opacity: [23, 61],
    tint: [44, 89],
    spraySpread: [300, 700],
    lineAngle: [-24, 36],
    lineLength: [500, 850],
    boxWidth: [430, 780],
    boxHeight: [360, 690]
  };
  for (const [key, [minimum, maximum]] of Object.entries(visualRanges)) {
    await setRandomRange(page, key, minimum, maximum);
  }
  await setRandomRange(page, "sequenceSpeed", 22, 39);
  await setRandomRange(page, "sequenceIntensity", 110, 180);
  assert.equal(await page.locator("#generatorSizeValue").textContent(), "300–420px");
  assert.equal(await page.locator("#generatorSequenceIntensityValue").textContent(), "110–180%");

  await generateWithSeed(page, 0x2468ace0, 96);
  const ranged = await getCompositionSnapshot(page);
  assertValuesWithin(ranged.sizeValues, 300, 420, "size");
  assertValuesWithin(ranged.rotationValues, -37, 41, "rotation");
  assertValuesWithin(ranged.opacityValues, 0.23, 0.61, "opacity");
  assertValuesWithin(ranged.tintValues, 0.44, 0.89, "color shift");
  assert.ok(new Set(ranged.sizeValues).size > 8, "expected varied randomized sizes");
  assert.ok(new Set(ranged.rotationValues).size > 8, "expected varied randomized rotations");
  assert.ok(new Set(ranged.opacityValues).size > 8, "expected varied randomized opacities");
  assert.ok(new Set(ranged.tintValues).size > 8, "expected varied randomized color shifts");
  assertValuesWithin(ranged.sampledGeometry.sampledSpacing, 90, 150, "spacing");
  assertValuesWithin(ranged.sampledGeometry.sampledLineLength, 500, 850, "line length");
  assertValuesWithin(ranged.sampledGeometry.sampledLineAngle, -24, 36, "line angle");
  assertValuesWithin(ranged.sampledGeometry.sampledSpraySpread, 300, 700, "spray spread");
  assertValuesWithin(ranged.sampledGeometry.sampledBoxWidth, 430, 780, "box width");
  assertValuesWithin(ranged.sampledGeometry.sampledBoxHeight, 360, 690, "box height");
  assertValuesWithin(ranged.sequenceSpeedValues, 22, 39, "sequence speed");
  assertValuesWithin(ranged.sequenceIntensityValues, 110, 180, "sequence intensity");
  assert.ok(new Set(ranged.sequenceSpeedValues).size > 1, "expected varied sequence speeds");
  assert.ok(new Set(ranged.sequenceIntensityValues).size > 1, "expected varied sequence intensities");

  const rangedSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.deepEqual(rangedSummary.randomRanges, Object.fromEntries(
    Object.entries(visualRanges).map(([key, [minimum, maximum]]) => [
      key,
      { minimum, maximum }
    ])
  ));
  assert.deepEqual(rangedSummary.sequenceRanges, {
    speed: { minimum: 22, maximum: 39 },
    intensity: { minimum: 110, maximum: 180 }
  });

  await generateWithSeed(page, 0x2468ace0, 96);
  const repeatedRange = await getCompositionSnapshot(page);
  assert.equal(repeatedRange.visualSignature, ranged.visualSignature);
  assert.equal(repeatedRange.sequenceSignature, ranged.sequenceSignature);
  assert.equal(repeatedRange.canvasBackground, ranged.canvasBackground);
  await generateWithSeed(page, 0x2468ace1, 96);
  assert.notEqual((await getCompositionSnapshot(page)).visualSignature, ranged.visualSignature);

  await page.locator("#generatorRandomizeAllToggle").check({ force: true });
  await page.locator("#generatorSequenceEnabledToggle").check({ force: true });
  await setPlacementModes(page, ["line", "spray", "box", "scatter"]);
  await page.locator('[data-canvas-size="800x1200"]').click();
  assert.deepEqual(
    await page.locator("#generatorCanvasWidthInput, #generatorCanvasHeightInput").evaluateAll(
      (inputs) => inputs.map((input) => input.value)
    ),
    ["800", "1200"]
  );
  await setSourceSelection(page, "category", ["radial"]);
  await setRange(page, "#generatorCountSlider", 60);
  await page.locator('.generator-margin-mode-choice:has(input[value="crop"]) span').click();
  const inspectButton = page.locator("#generatorCropInspectButton");
  assert.equal(await inspectButton.isVisible(), true);
  assert.equal(await inspectButton.isDisabled(), true);
  assert.equal(await inspectButton.textContent(), "set a margin to inspect");
  await setRange(page, "#generatorMarginSlider", 96);
  assert.match(await inspectButton.textContent(), /^(generate crop to inspect|inspect cropped gifs)$/);
  await setRange(page, "#generatorMarginSlider", 0);
  await generateWithSeed(page, 0x00c0ffee, 60);
  const uncropped = await getCompositionSnapshot(page);
  assert.equal(uncropped.overlay.hidden, true);

  await setRange(page, "#generatorMarginSlider", 96);
  assert.match(await inspectButton.textContent(), /^(generate crop to inspect|inspect cropped gifs)$/);
  await generateWithSeed(page, 0x00c0ffee, 60);
  const filtered = await getCompositionSnapshot(page);
  assert.equal(filtered.count, 60);
  assert.equal(filtered.uniqueSourceCount, 60);
  assert.deepEqual(filtered.categories, ["radial"]);
  assert.equal(filtered.sequenceCount, 60);
  assert.equal(filtered.coordinateWidth, 800);
  assert.equal(filtered.coordinateHeight, 1200);
  assert.equal(filtered.outOfBounds, 0);
  assert.equal(await page.locator("#generatorMarginSlider").getAttribute("max"), "360");
  assert.equal(filtered.margin, 96);
  assert.equal(filtered.marginMode, "crop");
  assert.equal(filtered.signature, uncropped.signature);
  assert.equal(filtered.overlay.hidden, false);
  assert.equal(filtered.overlay.borderWidth, "96px");
  assert.equal(filtered.overlay.borderColor, filtered.canvasBackground);
  assert.equal(filtered.overlay.pointerEvents, "none");
  assert.equal(filtered.overlay.parentId, "generatorComposition");
  assert.ok(filtered.overlay.zIndex > filtered.maximumStampZIndex);
  assert.ok(filtered.croppedCenterCount > 0);
  assert.match(filtered.canvasAriaLabel, /96 pixel cropped margin/i);

  assert.equal(await inspectButton.isVisible(), true);
  assert.equal(await inspectButton.isEnabled(), true);
  assert.equal(await inspectButton.getAttribute("aria-pressed"), "false");
  await inspectButton.click();
  await page.waitForFunction(() => window.GeneratorApp.getSummary().cropInspectionActive);
  const inspectionState = await page.evaluate(() => {
    const stamps = Array.from(document.querySelectorAll(".generator-stamp"));
    return {
      pausedAnimations: stamps.filter(
        (stamp) => getComputedStyle(stamp).animationPlayState === "paused"
      ).length,
      frozenSources: stamps.filter(
        (stamp) => Boolean(stamp.dataset.cropInspectionPausedSrc)
      ).length,
      interactive: stamps.filter((stamp) => getComputedStyle(stamp).pointerEvents === "auto").length,
      overlayOpacity: Number(getComputedStyle(document.getElementById("generatorMarginOverlay")).opacity)
    };
  });
  assert.equal(inspectionState.pausedAnimations, 60);
  assert.equal(inspectionState.interactive, 60);
  assert.ok(inspectionState.frozenSources > 0, "expected loaded GIFs to use paused still frames");
  assert.ok(inspectionState.overlayOpacity > 0 && inspectionState.overlayOpacity < 1);

  const croppedStampIndex = await page.locator(".generator-stamp").evaluateAll((stamps) => {
    const canvas = document.getElementById("generatorCanvas");
    const margin = Number(canvas?.dataset.generatorMargin || 0);
    const width = Number.parseFloat(document.getElementById("generatorComposition")?.style.width || "0");
    const height = Number.parseFloat(document.getElementById("generatorComposition")?.style.height || "0");
    const match = stamps.find((stamp) => {
      const x = Number(stamp.dataset.generatorX);
      const y = Number(stamp.dataset.generatorY);
      return x < margin || x > width - margin || y < margin || y > height - margin;
    });
    return match?.dataset.generatorIndex || stamps[0]?.dataset.generatorIndex || "";
  });
  const croppedStamp = page.locator(`.generator-stamp[data-generator-index="${croppedStampIndex}"]`);
  await croppedStamp.evaluate((stamp) => stamp.click());
  assert.equal(await croppedStamp.getAttribute("data-generator-uncropped"), "true");
  assert.equal(await croppedStamp.getAttribute("aria-pressed"), "true");
  assert.equal((await page.evaluate(() => window.GeneratorApp.getSummary())).uncroppedCount, 1);
  assert.ok(
    Number(await croppedStamp.evaluate((stamp) => getComputedStyle(stamp).zIndex)) > filtered.overlay.zIndex
  );

  await inspectButton.click();
  await page.waitForFunction(() => !window.GeneratorApp.getSummary().cropInspectionActive);
  assert.equal(await croppedStamp.getAttribute("data-generator-uncropped"), "true");
  assert.equal(await croppedStamp.getAttribute("data-crop-inspection-paused-src"), null);
  assert.equal(await page.locator("#generatorCanvas").evaluate(
    (canvas) => canvas.classList.contains("crop-inspection-active")
  ), false);
  assert.equal(await inspectButton.textContent(), "edit uncropped gifs (1)");
  assert.match(await page.locator("#generatorCropInspectStatus").textContent(), /1 gif remains uncropped/i);

  const primaryActionGeometry = await page.evaluate(() => {
    const sidebar = document.getElementById("controls");
    const dock = document.getElementById("generatorWorkspaceActions")?.getBoundingClientRect();
    const modeBar = document.getElementById("mainModeBar")?.getBoundingClientRect();
    const generate = document.getElementById("generatorGenerateButton")?.getBoundingClientRect();
    const background = document.getElementById("generatorBackgroundButton")?.getBoundingClientRect();
    const bookmark = document.getElementById("generatorBookmarkButton")?.getBoundingClientRect();
    const download = document.querySelector(".generator-download-split")?.getBoundingClientRect();
    return {
      buttonsOutsideSidebar: [
        "generatorGenerateButton",
        "generatorBackgroundButton",
        "generatorBookmarkButton",
        "generatorDownloadWebpButton",
        "generatorDownloadMp4Button"
      ].every((id) => !sidebar?.contains(document.getElementById(id))),
      sameRow: [background, bookmark, download].every(
        (rect) => Math.abs(rect.top - generate.top) < 0.5 && Math.abs(rect.bottom - generate.bottom) < 0.5
      ),
      ordered: generate.left > background.right &&
        bookmark.left > generate.right &&
        download.left > bookmark.right,
      dockBeforeModeBar: dock.right < modeBar.left,
      alignedToModeBar: Math.abs(dock.bottom - modeBar.bottom) < 0.5,
      dockWidth: dock.width,
      backgroundWidth: background.width,
      backgroundHeight: background.height
    };
  });
  assert.equal(primaryActionGeometry.buttonsOutsideSidebar, true);
  assert.equal(primaryActionGeometry.sameRow, true);
  assert.equal(primaryActionGeometry.ordered, true);
  assert.equal(primaryActionGeometry.dockBeforeModeBar, true);
  assert.equal(primaryActionGeometry.alignedToModeBar, true);
  assert.equal(primaryActionGeometry.dockWidth, 190);
  assert.ok(Math.abs(primaryActionGeometry.backgroundWidth - primaryActionGeometry.backgroundHeight) < 0.1);
  assert.equal(await page.locator('button[aria-label="Generator mode"]').count(), 0);
  assert.equal(await page.locator("#generatorActionStatus").evaluate((status) => (
    getComputedStyle(status).clipPath === "inset(50%)"
  )), true);

  const dynamicBaseline = await getCompositionSnapshot(page);
  const dynamicBaselineSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  const backgroundChanged = await page.evaluate(() => window.GeneratorApp.randomizeBackground());
  assert.equal(backgroundChanged, true);
  const backgroundOnlySnapshot = await getCompositionSnapshot(page);
  const backgroundOnlySummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.notEqual(backgroundOnlySnapshot.canvasBackground, dynamicBaseline.canvasBackground);
  assert.equal(backgroundOnlySnapshot.visualSignature, dynamicBaseline.visualSignature);
  assert.equal(backgroundOnlySnapshot.sourceIndexSignature, dynamicBaseline.sourceIndexSignature);
  assert.equal(backgroundOnlySummary.seed, dynamicBaselineSummary.seed);
  assert.equal(backgroundOnlySummary.historyDepth, Math.min(30, dynamicBaselineSummary.historyDepth + 1));

  const undoButton = page.locator("#generatorUndoButton");
  assert.equal(await undoButton.isVisible(), true);
  await undoButton.click();
  await page.waitForFunction(
    (background) => window.GeneratorApp.getSummary().backgroundColor === background,
    dynamicBaselineSummary.backgroundColor
  );
  assert.equal((await getCompositionSnapshot(page)).visualSignature, dynamicBaseline.visualSignature);

  await setRange(page, "#generatorMarginSlider", 118);
  await page.waitForFunction(() =>
    document.getElementById("generatorCanvas")?.getAttribute("aria-busy") === "false" &&
    window.GeneratorApp.getSummary().margin === 118
  );
  const dynamicallyUpdated = await getCompositionSnapshot(page);
  const dynamicallyUpdatedSummary = await page.evaluate(() => window.GeneratorApp.getSummary());
  assert.equal(dynamicallyUpdated.margin, 118);
  assert.equal(dynamicallyUpdated.sourceIndexSignature, dynamicBaseline.sourceIndexSignature);
  assert.equal(dynamicallyUpdatedSummary.seed, dynamicBaselineSummary.seed);
  assert.equal(dynamicallyUpdatedSummary.uncroppedCount, dynamicBaselineSummary.uncroppedCount);
  await undoButton.click();
  await page.waitForFunction(() => window.GeneratorApp.getSummary().margin === 96);
  assert.equal((await getCompositionSnapshot(page)).sourceIndexSignature, dynamicBaseline.sourceIndexSignature);

  await generateWithSeed(page, 0x12344321, 60);
  assert.notEqual((await page.evaluate(() => window.GeneratorApp.getSummary())).seed, dynamicBaselineSummary.seed);
  await undoButton.click();
  await page.waitForFunction(
    (seed) => window.GeneratorApp.getSummary().seed === seed,
    dynamicBaselineSummary.seed
  );
  const generationUndone = await getCompositionSnapshot(page);
  assert.equal(generationUndone.visualSignature, dynamicBaseline.visualSignature);
  assert.equal(generationUndone.canvasBackground, dynamicBaseline.canvasBackground);
  assert.equal((await page.evaluate(() => window.GeneratorApp.getSummary())).historyLimit, 30);

  await page.evaluate(() => {
    window.__generatorSequenceIsolationNodes = Array.from(
      document.querySelectorAll(".generator-stamp")
    );
  });
  const beforeSequenceSpeedChange = await getCompositionSnapshot(page);
  await setRandomRange(page, "sequenceSpeed", 57, 57);
  await page.waitForFunction(() => {
    const range = window.GeneratorApp.getSummary().sequenceRanges.speed;
    return range?.minimum === 57 && range?.maximum === 57;
  });
  const afterSequenceSpeedChange = await getCompositionSnapshot(page);
  assert.equal(
    afterSequenceSpeedChange.nonSequenceVisualSignature,
    beforeSequenceSpeedChange.nonSequenceVisualSignature
  );
  assert.equal(
    afterSequenceSpeedChange.sourceIndexSignature,
    beforeSequenceSpeedChange.sourceIndexSignature
  );
  assert.deepEqual(
    afterSequenceSpeedChange.sequenceAssignments.map(({ effect, timing, intensity }) => ({
      effect,
      timing,
      intensity
    })),
    beforeSequenceSpeedChange.sequenceAssignments.map(({ effect, timing, intensity }) => ({
      effect,
      timing,
      intensity
    }))
  );
  assert.ok(afterSequenceSpeedChange.sequenceSpeedValues.every((value) => value === 57));
  assert.equal(
    await page.evaluate(() => window.__generatorSequenceIsolationNodes.every(
      (node, index) => node === document.querySelectorAll(".generator-stamp")[index]
    )),
    true,
    "expected sequence speed changes to retain every live GIF node"
  );

  const beforeSequenceIntensityChange = afterSequenceSpeedChange;
  await setRandomRange(page, "sequenceIntensity", 205, 205);
  await page.waitForFunction(() => {
    const range = window.GeneratorApp.getSummary().sequenceRanges.intensity;
    return range?.minimum === 205 && range?.maximum === 205;
  });
  const afterSequenceIntensityChange = await getCompositionSnapshot(page);
  assert.equal(
    afterSequenceIntensityChange.nonSequenceVisualSignature,
    beforeSequenceIntensityChange.nonSequenceVisualSignature
  );
  assert.deepEqual(
    afterSequenceIntensityChange.sequenceAssignments.map(({ effect, timing, speed }) => ({
      effect,
      timing,
      speed
    })),
    beforeSequenceIntensityChange.sequenceAssignments.map(({ effect, timing, speed }) => ({
      effect,
      timing,
      speed
    }))
  );
  assert.ok(afterSequenceIntensityChange.sequenceIntensityValues.every((value) => value === 205));

  const effectToDisable = afterSequenceIntensityChange.sequenceAssignments[0]?.effect;
  assert.ok(effectToDisable, "expected a sequence effect to test in-place reassignment");
  const beforeSequenceEffectChange = afterSequenceIntensityChange;
  await page.locator(
    `.generator-sequence-effect-checkbox[value="${effectToDisable}"]`
  ).uncheck({ force: true });
  await page.waitForFunction(
    (effect) => !Object.prototype.hasOwnProperty.call(
      window.GeneratorApp.getSummary().sequenceEffectCounts,
      effect
    ),
    effectToDisable
  );
  const afterSequenceEffectChange = await getCompositionSnapshot(page);
  assert.equal(
    afterSequenceEffectChange.nonSequenceVisualSignature,
    beforeSequenceEffectChange.nonSequenceVisualSignature
  );
  assert.equal(
    afterSequenceEffectChange.sourceIndexSignature,
    beforeSequenceEffectChange.sourceIndexSignature
  );
  assert.deepEqual(
    afterSequenceEffectChange.sequenceAssignments.map(({ speed, intensity }) => ({
      speed,
      intensity
    })),
    beforeSequenceEffectChange.sequenceAssignments.map(({ speed, intensity }) => ({
      speed,
      intensity
    }))
  );
  assert.equal(
    await page.evaluate(() => window.__generatorSequenceIsolationNodes.every(
      (node, index) => node === document.querySelectorAll(".generator-stamp")[index]
    )),
    true,
    "expected sequence effect changes to retain every live GIF node"
  );

  await page.setViewportSize({ width: 390, height: 844 });
  await page.waitForTimeout(50);
  const mobileLayout = await page.evaluate(() => {
    const controls = document.getElementById("controls")?.getBoundingClientRect();
    const range = document.querySelector('[data-random-range="size"]')?.getBoundingClientRect();
    return {
      viewportWidth: document.documentElement.clientWidth,
      scrollWidth: document.documentElement.scrollWidth,
      controlsLeft: controls?.left || 0,
      controlsRight: controls?.right || 0,
      rangeWidth: range?.width || 0
    };
  });
  assert.ok(mobileLayout.scrollWidth <= mobileLayout.viewportWidth + 1);
  assert.ok(mobileLayout.controlsLeft >= 0 && mobileLayout.controlsRight <= mobileLayout.viewportWidth + 1);
  assert.ok(mobileLayout.rangeWidth > 200, "expected usable dual ranges on mobile");

  assert.deepEqual(errors, []);
  process.stdout.write(
    `generator regression checks passed (${initial.count} default / ${filtered.count} filtered stamps; categories, tags, and sequences verified)\n`
  );
} finally {
  await context.close();
  await browser.close();
  await new Promise((resolveClose) => localServer.server.close(resolveClose));
}
