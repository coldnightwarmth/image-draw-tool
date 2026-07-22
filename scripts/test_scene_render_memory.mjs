#!/usr/bin/env node

import assert from "node:assert/strict";

import {
  calculateAvailableBitmapBytes,
  sumReadySourceBitmapBytes,
} from "../scene-render-worker.js";

const mib = 1024 * 1024;
const budget = 256 * mib;
const canvasBytes = 16 * mib;
const retainedOldSourceBytes = 96 * mib;
const otherDecodeReservations = 32 * mib;

const retainedBytes = sumReadySourceBitmapBytes([
  {
    status: "ready",
    replacementPending: true,
    data: { estimatedBitmapBytes: retainedOldSourceBytes },
  },
  { status: "ready", data: { estimatedBitmapBytes: 8 * mib } },
  { status: "loading", data: { estimatedBitmapBytes: 100 * mib } },
]);
assert.equal(
  retainedBytes,
  104 * mib,
  "Every ready source must remain counted while an LOD replacement is pending."
);

const replacementAvailableBytes = calculateAvailableBitmapBytes(
  budget,
  canvasBytes,
  retainedOldSourceBytes,
  otherDecodeReservations
);
assert.equal(replacementAvailableBytes, 112 * mib);
assert.ok(
  120 * mib > replacementAvailableBytes,
  "A replacement that would exceed the old+new peak must be rejected."
);

const incorrectlyOmittingOldSource = calculateAvailableBitmapBytes(
  budget,
  canvasBytes,
  0,
  otherDecodeReservations
);
assert.equal(incorrectlyOmittingOldSource, 208 * mib);
assert.ok(
  120 * mib <= incorrectlyOmittingOldSource,
  "The fixture must demonstrate why omitting the retained source was unsafe."
);

assert.equal(calculateAvailableBitmapBytes(10, 8, 8, 8), 0);
assert.equal(calculateAvailableBitmapBytes(10.9, 1.2, 2.8, 3.1), 4);

console.log("Scene renderer peak-memory accounting checks passed.");
