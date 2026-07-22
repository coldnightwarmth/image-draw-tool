#!/usr/bin/env node

import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import path from "node:path";
import vm from "node:vm";
import { fileURLToPath } from "node:url";

const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const projectDirectory = path.resolve(scriptDirectory, "..");
const appSource = await readFile(path.join(projectDirectory, "app.js"), "utf8");

function extractFunctionSource(name) {
  const start = appSource.indexOf(`function ${name}(`);
  assert.notEqual(start, -1, `Could not find ${name} in app.js.`);
  const bodyStart = appSource.indexOf("{", start);
  let depth = 0;
  let quote = "";
  let escaped = false;
  for (let index = bodyStart; index < appSource.length; index += 1) {
    const character = appSource[index];
    if (quote) {
      if (escaped) {
        escaped = false;
      } else if (character === "\\") {
        escaped = true;
      } else if (character === quote) {
        quote = "";
      }
      continue;
    }
    if (character === '"' || character === "'" || character === "`") {
      quote = character;
    } else if (character === "{") {
      depth += 1;
    } else if (character === "}") {
      depth -= 1;
      if (depth === 0) {
        return appSource.slice(start, index + 1);
      }
    }
  }
  assert.fail(`Could not find the end of ${name} in app.js.`);
}

function evaluateFunction(name, globals = {}) {
  const context = vm.createContext({ ...globals });
  vm.runInContext(`${extractFunctionSource(name)}; this.result = ${name};`, context);
  return context.result;
}

const isGifInspectCapabilityError = evaluateFunction("isGifInspectCapabilityError");
assert.equal(
  isGifInspectCapabilityError({ category: "capability", code: "UNSUPPORTED_VERSION" }),
  true
);
assert.equal(
  isGifInspectCapabilityError({ category: "safety", code: "INPUT_TOO_LARGE" }),
  false,
  "Hard safety failures must not enter the main-thread fallback."
);
assert.equal(
  isGifInspectCapabilityError({ category: "cancelled", code: "GIF_INSPECTION_CANCELLED" }),
  false
);

const frameCountQueueSource = extractFunctionSource("runBrushFrameCountQueue");
assert.doesNotMatch(
  frameCountQueueSource,
  /decodeGifAnimation\s*\(/,
  "Brush metadata inspection must not fall back to full-frame GIF decoding."
);
assert.match(frameCountQueueSource, /inspectGifFrameCountOnMainThreadBounded\s*\(/);

let stockMetadata = null;
const exportRasterSourceRequiresLiveBrowserFrame = evaluateFunction(
  "exportRasterSourceRequiresLiveBrowserFrame",
  {
    getStockBrushMetadataForSource: () => stockMetadata,
    findBrushById: () => null,
    isGifUrl: (source) => /\.gif(?:[?#]|$)/i.test(source),
    getBrushSourceIsGif: () => false,
    getSceneRendererMimeType: (source) => {
      if (/\.png(?:[?#]|$)/i.test(source)) return "image/png";
      if (/\.webp(?:[?#]|$)/i.test(source)) return "image/webp";
      if (/\.avif(?:[?#]|$)/i.test(source)) return "image/avif";
      if (/\.gif(?:[?#]|$)/i.test(source)) return "image/gif";
      return "";
    },
    getBrushPrimarySourceUrl: () => "",
  }
);

stockMetadata = { animated: true };
assert.equal(exportRasterSourceRequiresLiveBrowserFrame("brush.apng.png"), true);
assert.equal(exportRasterSourceRequiresLiveBrowserFrame("brush.webp"), true);
assert.equal(exportRasterSourceRequiresLiveBrowserFrame("brush.avif"), true);
assert.equal(
  exportRasterSourceRequiresLiveBrowserFrame("brush.gif"),
  false,
  "Existing GIF worker acceleration must remain eligible."
);

stockMetadata = { animated: false };
assert.equal(exportRasterSourceRequiresLiveBrowserFrame("brush.png"), false);

console.log("GIF inspection and export raster policy checks passed.");
