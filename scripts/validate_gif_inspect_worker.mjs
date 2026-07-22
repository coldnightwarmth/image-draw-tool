#!/usr/bin/env node

import assert from "node:assert/strict";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";

import { inspectGifArrayBuffer } from "../gif-inspect-worker.js";

const scriptDirectory = path.dirname(fileURLToPath(import.meta.url));
const projectDirectory = path.resolve(scriptDirectory, "..");

async function findSampleGifs(directory, limit, matches = []) {
  if (matches.length >= limit) {
    return matches;
  }
  const entries = await readdir(directory, { withFileTypes: true });
  entries.sort((a, b) => a.name.localeCompare(b.name));
  for (const entry of entries) {
    if (matches.length >= limit) {
      break;
    }
    const entryPath = path.join(directory, entry.name);
    if (entry.isDirectory()) {
      await findSampleGifs(entryPath, limit, matches);
    } else if (entry.isFile() && entry.name.toLowerCase().endsWith(".gif")) {
      matches.push(entryPath);
    }
  }
  return matches;
}

const requestedPaths = process.argv.slice(2).map((value) => path.resolve(value));
const gifPaths = requestedPaths.length
  ? requestedPaths
  : await findSampleGifs(path.join(projectDirectory, "brushes"), 3);

assert.ok(gifPaths.length > 0, "No GIF files were provided or found under brushes/.");

const safetyLimitFixture = new Uint8Array(14);
safetyLimitFixture.set([0x47, 0x49, 0x46, 0x38, 0x39, 0x61]);
await assert.rejects(
  inspectGifArrayBuffer(safetyLimitFixture.buffer, {
    checkOpacity: false,
    maxInputBytes: 13,
  }),
  (error) => {
    assert.equal(error?.code, "INPUT_TOO_LARGE");
    assert.equal(error?.category, "safety");
    assert.equal(error?.retriable, false);
    return true;
  },
  "Input byte-limit failures must remain typed hard-safety errors."
);

const cancelledController = new AbortController();
cancelledController.abort();
await assert.rejects(
  inspectGifArrayBuffer(safetyLimitFixture.buffer, { checkOpacity: false }, cancelledController.signal),
  (error) => error?.name === "AbortError",
  "Cancellation must remain distinguishable from inspection failures."
);

for (const gifPath of gifPaths) {
  const bytes = await readFile(gifPath);
  const buffer = bytes.buffer.slice(bytes.byteOffset, bytes.byteOffset + bytes.byteLength);
  const result = await inspectGifArrayBuffer(buffer);

  assert.ok(result.width > 0, "width must be positive");
  assert.ok(result.height > 0, "height must be positive");
  assert.ok(result.frameCount > 0, "frameCount must be positive");
  assert.equal(result.frameDelaysMs.length, result.frameCount);
  assert.equal(
    result.frameDelaysMs.reduce((total, delay) => total + delay, 0),
    result.totalDurationMs
  );
  assert.equal(result.animated, result.frameCount > 1);
  assert.ok([true, false, null].includes(result.opaque));

  console.log(
    JSON.stringify({
      file: path.relative(projectDirectory, gifPath),
      width: result.width,
      height: result.height,
      frameCount: result.frameCount,
      totalDurationMs: result.totalDurationMs,
      opaque: result.opaque,
      opacityMethod: result.opacity.method,
    })
  );
}
