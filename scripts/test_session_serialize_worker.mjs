import assert from "node:assert/strict";
import fs from "node:fs";
import vm from "node:vm";

const source = fs.readFileSync(new URL("../session-serialize-worker.js", import.meta.url), "utf8");
const replies = [];
let messageHandler = null;
const workerScope = {
  addEventListener(type, handler) {
    if (type === "message") messageHandler = handler;
  },
  postMessage(message) {
    replies.push(message);
  }
};
vm.runInNewContext(source, { self: workerScope, Map, Set, Array, Number, JSON, Error });
assert.equal(typeof messageHandler, "function");

function send(data) {
  replies.length = 0;
  messageHandler({ data });
  assert.equal(replies.length, 1);
  return replies[0];
}

const base = { version: 1, brushes: [{ id: 1, url: "active.gif" }] };
const first = send({
  type: "serialize-incremental",
  requestId: 1,
  base,
  strokeOrder: ["a", "b"],
  redoStrokeOrder: [],
  updates: [
    {
      token: "a",
      revision: 0,
      snapshot: { id: 7, stamps: [{ brushId: 1 }] },
      brushSources: [{ id: 1, url: "active.gif" }]
    },
    {
      token: "b",
      revision: 0,
      snapshot: { id: 7, stamps: [{ brushId: 9 }] },
      brushSources: [{ id: 9, url: "missing.gif", name: "missing", width: 5, height: 6 }]
    }
  ]
});
assert.equal(first.type, "serialized");
const firstSnapshot = JSON.parse(first.json);
assert.deepEqual(firstSnapshot.strokes.map((stroke) => stroke.stamps[0].brushId), [1, 9]);
assert.deepEqual(firstSnapshot.strokeBrushes, [
  { id: 9, url: "missing.gif", name: "missing", width: 5, height: 6 }
]);

const reordered = send({
  type: "serialize-incremental",
  requestId: 2,
  base: { ...base, camera: { x: 4, y: 5, scale: 2 } },
  strokeOrder: ["b"],
  redoStrokeOrder: ["a"],
  updates: []
});
assert.equal(reordered.type, "serialized");
const reorderedSnapshot = JSON.parse(reordered.json);
assert.equal(reorderedSnapshot.strokes[0].stamps[0].brushId, 9);
assert.equal(reorderedSnapshot.redoStrokes[0].stamps[0].brushId, 1);
assert.equal(reorderedSnapshot.camera.scale, 2);

const pruned = send({
  type: "serialize-incremental",
  requestId: 3,
  base,
  strokeOrder: ["b"],
  redoStrokeOrder: [],
  updates: [{
    token: "b",
    revision: 1,
    snapshot: { id: 7, hidden: true, stamps: [{ brushId: 9 }] },
    brushSources: [{ id: 9, url: "missing.gif", name: "missing", width: 5, height: 6 }]
  }]
});
assert.equal(JSON.parse(pruned.json).strokes[0].hidden, true);

const missingPrunedToken = send({
  type: "serialize-incremental",
  requestId: 4,
  base,
  strokeOrder: ["a"],
  redoStrokeOrder: [],
  updates: []
});
assert.equal(missingPrunedToken.type, "error");

console.log("session serialize worker tests passed");
