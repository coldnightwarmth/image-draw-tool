"use strict";

const assert = require("node:assert/strict");
const SceneOcclusion = require("../scene-occlusion.js");

const VIEWPORT = { x: 0, y: 0, width: 100, height: 100 };

function opaque(id, x, y, width, height, extra = {}) {
  return {
    id,
    x,
    y,
    width,
    height,
    cullable: true,
    opaque: true,
    opacity: 1,
    blendMode: "normal",
    filter: "none",
    effects: false,
    axisAligned: true,
    ...extra,
  };
}

function translucent(id, x, y, width, height, extra = {}) {
  return {
    id,
    x,
    y,
    width,
    height,
    cullable: true,
    opaque: false,
    opacity: 0.5,
    blendMode: "normal",
    filter: "none",
    effects: false,
    axisAligned: true,
    ...extra,
  };
}

function ids(result) {
  return [...result.occludedIds].sort();
}

function test(name, callback) {
  try {
    callback();
    process.stdout.write(`ok - ${name}\n`);
  } catch (error) {
    process.stderr.write(`not ok - ${name}\n`);
    throw error;
  }
}

test("exact containment culls a lower stamp", () => {
  const lower = opaque("lower", 20, 20, 10, 10);
  const upper = opaque("upper", 10, 10, 30, 30);
  const result = SceneOcclusion.compute([lower, upper], {
    viewport: VIEWPORT,
    tileSize: 64,
  });
  assert.deepEqual(ids(result), ["lower"]);
  assert.equal(result.occludedEntries[0].reason, "exact-containment");
  assert.equal(result.occludedEntries[0].coveringId, "upper");
});

test("partial overlap is never treated as full coverage", () => {
  const result = SceneOcclusion.compute(
    [opaque("lower", 10, 10, 40, 40), opaque("upper", 10, 10, 20, 40)],
    { viewport: VIEWPORT, tileSize: 10 }
  );
  assert.deepEqual(ids(result), []);
});

test("aligned opaque rectangles can cover a lower stamp as a union", () => {
  const result = SceneOcclusion.compute(
    [
      opaque("lower", 0, 0, 100, 100),
      opaque("upper-left", 0, 0, 50, 100),
      opaque("upper-right", 50, 0, 50, 100),
    ],
    { viewport: VIEWPORT, tileSize: 25 }
  );
  assert.deepEqual(ids(result), ["lower"]);
  assert.equal(result.occludedEntries[0].reason, "tile-coverage");
});

test("a one-pixel gap in a union prevents culling", () => {
  const result = SceneOcclusion.compute(
    [
      opaque("lower", 0, 0, 100, 100),
      opaque("upper-left", 0, 0, 49, 100),
      opaque("upper-right", 50, 0, 50, 100),
    ],
    { viewport: VIEWPORT, tileSize: 10 }
  );
  assert.deepEqual(ids(result), []);
});

test("translucent and uncertain records do not occlude", () => {
  const result = SceneOcclusion.compute(
    [
      opaque("lower", 10, 10, 20, 20),
      translucent("translucent", 0, 0, 100, 100),
      opaque("rotated", 0, 0, 100, 100, { axisAligned: false }),
      opaque("filtered", 0, 0, 100, 100, { filter: "blur(1px)" }),
    ],
    { viewport: VIEWPORT, tileSize: 10 }
  );
  assert.deepEqual(ids(result), []);
  // The lower record itself is eligible once the scan reaches it; none of the
  // three uncertain records above it are.
  assert.equal(result.stats.eligibleOccluderCount, 1);
});

test("occluderEligible is an explicit pre-certified fast path", () => {
  const result = SceneOcclusion.compute(
    [
      opaque("lower", 10, 10, 20, 20),
      { id: "upper", x: 0, y: 0, width: 100, height: 100, occluderEligible: true },
    ],
    { viewport: VIEWPORT }
  );
  assert.deepEqual(ids(result), ["lower"]);
});

test("targets require explicit cullable eligibility", () => {
  const lower = opaque("lower", 10, 10, 20, 20, { cullable: false });
  const result = SceneOcclusion.compute([lower, opaque("upper", 0, 0, 100, 100)], {
    viewport: VIEWPORT,
  });
  assert.deepEqual(ids(result), []);
});

test("custom record, ID, occluder, and cullable accessors are supported", () => {
  const records = [
    { key: "lower", box: [10, 10, 20, 20], kind: "target" },
    { key: "upper", box: [0, 0, 100, 100], kind: "solid" },
  ];
  const result = SceneOcclusion.compute(records, {
    viewport: VIEWPORT,
    rectOf: (record) => ({
      x: record.box[0],
      y: record.box[1],
      width: record.box[2],
      height: record.box[3],
    }),
    idOf: (record) => record.key,
    isOccluder: (record) => record.kind === "solid",
    isCullable: (record) => record.kind === "target",
  });
  assert.deepEqual(ids(result), ["lower"]);
});

test("top-to-bottom input order is supported", () => {
  const upper = opaque("upper", 0, 0, 100, 100);
  const lower = opaque("lower", 10, 10, 20, 20);
  const result = SceneOcclusion.compute([upper, lower], {
    viewport: VIEWPORT,
    order: "top-to-bottom",
  });
  assert.deepEqual(ids(result), ["lower"]);
});

test("a target that extends outside the viewport is retained", () => {
  const result = SceneOcclusion.compute(
    [opaque("lower", -10, 10, 20, 20), opaque("upper", -10, 0, 50, 50)],
    { viewport: VIEWPORT }
  );
  assert.deepEqual(ids(result), []);
});

test("negative dimensions are normalized", () => {
  const result = SceneOcclusion.compute(
    [opaque("lower", 30, 30, -10, -10), opaque("upper", 10, 10, 40, 40)],
    { viewport: VIEWPORT }
  );
  assert.deepEqual(ids(result), ["lower"]);
});

test("invalid ordering is rejected", () => {
  assert.throws(
    () => SceneOcclusion.compute([], { viewport: VIEWPORT, order: "sideways" }),
    /order must be/
  );
});

test("invalid viewport produces a safe empty result", () => {
  const result = SceneOcclusion.compute([opaque("lower", 0, 0, 10, 10)], {});
  assert.deepEqual(ids(result), []);
  assert.equal(result.stats.columns, 0);
});

function exactUnionCovers(target, rectangles) {
  const clipped = rectangles
    .map((rect) => ({
      left: Math.max(target.left, rect.left),
      top: Math.max(target.top, rect.top),
      right: Math.min(target.right, rect.right),
      bottom: Math.min(target.bottom, rect.bottom),
    }))
    .filter((rect) => rect.right > rect.left && rect.bottom > rect.top);
  const xs = [...new Set([
    target.left,
    target.right,
    ...clipped.flatMap((rect) => [rect.left, rect.right]),
  ])].sort((a, b) => a - b);

  for (let xIndex = 0; xIndex < xs.length - 1; xIndex += 1) {
    const left = xs[xIndex];
    const right = xs[xIndex + 1];
    if (!(right > left)) continue;

    const intervals = clipped
      .filter((rect) => rect.left <= left && rect.right >= right)
      .map((rect) => [rect.top, rect.bottom])
      .sort((a, b) => a[0] - b[0]);
    let coveredTo = target.top;
    for (const interval of intervals) {
      if (interval[0] > coveredTo) break;
      coveredTo = Math.max(coveredTo, interval[1]);
      if (coveredTo >= target.bottom) break;
    }
    if (coveredTo < target.bottom) return false;
  }
  return true;
}

function makeRandom(seed) {
  let state = seed >>> 0;
  return () => {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    return state / 0x100000000;
  };
}

test("randomized property check: every culled record is exactly covered", () => {
  const random = makeRandom(0xc0111de);
  for (let pass = 0; pass < 150; pass += 1) {
    const records = [];
    for (let index = 0; index < 35; index += 1) {
      const x = Math.floor(random() * 18) * 5;
      const y = Math.floor(random() * 18) * 5;
      const width = (1 + Math.floor(random() * 10)) * 5;
      const height = (1 + Math.floor(random() * 10)) * 5;
      records.push(
        opaque(`stamp-${index}`, x, y, Math.min(width, 100 - x), Math.min(height, 100 - y), {
          opaque: random() > 0.25,
        })
      );
    }

    const result = SceneOcclusion.compute(records, {
      viewport: VIEWPORT,
      tileSize: 5 + Math.floor(random() * 20),
      maxCells: 400,
    });

    for (const entry of result.occludedEntries) {
      const upperRecords = records.slice(entry.index + 1).filter((record) => {
        return record.opaque === true && !result.occludedIds.has(record.id);
      });
      const upperRects = upperRecords.map((record) =>
        SceneOcclusion.normalizeRect(record)
      );
      assert.equal(
        exactUnionCovers(entry.rect, upperRects),
        true,
        `${entry.id} was not exactly covered on randomized pass ${pass}`
      );
    }
  }
});

process.stdout.write("scene occlusion tests passed\n");
