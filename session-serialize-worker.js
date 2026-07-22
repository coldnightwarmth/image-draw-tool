const strokeMirror = new Map();

function requireToken(value) {
  const token = typeof value === "string" ? value : "";
  if (!token) {
    throw new Error("Session stroke token is missing.");
  }
  return token;
}

function normalizeOrder(value, label) {
  if (!Array.isArray(value)) {
    throw new Error(`${label} must be an array.`);
  }
  const order = value.map(requireToken);
  if (new Set(order).size !== order.length) {
    throw new Error(`${label} contains a duplicate stroke token.`);
  }
  return order;
}

function collectStrokeBrushSources(base, stagedMirror, strokeOrder, redoStrokeOrder) {
  const currentBrushIds = new Set(
    (Array.isArray(base.brushes) ? base.brushes : [])
      .map((brush) => Number(brush?.id))
      .filter((id) => Number.isFinite(id))
  );
  const byId = new Map();
  for (const token of [...strokeOrder, ...redoStrokeOrder]) {
    const entry = stagedMirror.get(token);
    for (const descriptor of Array.isArray(entry?.brushSources) ? entry.brushSources : []) {
      const brushId = Number(descriptor?.id);
      if (
        !Number.isFinite(brushId) ||
        currentBrushIds.has(brushId) ||
        byId.has(brushId) ||
        !descriptor?.url
      ) {
        continue;
      }
      byId.set(brushId, {
        id: brushId,
        url: descriptor.url,
        name: descriptor.name,
        width: descriptor.width,
        height: descriptor.height
      });
    }
  }
  return Array.from(byId.values());
}

function serializeIncremental(message) {
  const base = message.base;
  if (!base || typeof base !== "object" || Array.isArray(base)) {
    throw new Error("Session snapshot base is invalid.");
  }
  const strokeOrder = normalizeOrder(message.strokeOrder, "strokeOrder");
  const redoStrokeOrder = normalizeOrder(message.redoStrokeOrder, "redoStrokeOrder");
  const stagedMirror = new Map(strokeMirror);

  for (const update of Array.isArray(message.updates) ? message.updates : []) {
    const token = requireToken(update?.token);
    const revision = Number(update?.revision);
    if (!Number.isFinite(revision) || !update?.snapshot || typeof update.snapshot !== "object") {
      throw new Error(`Session stroke update ${token} is invalid.`);
    }
    const snapshotJson = JSON.stringify(update.snapshot);
    if (typeof snapshotJson !== "string") {
      throw new Error(`Session stroke update ${token} cannot be serialized.`);
    }
    stagedMirror.set(token, {
      revision,
      snapshotJson,
      brushSources: Array.isArray(update.brushSources) ? update.brushSources : []
    });
  }

  const activeTokens = new Set([...strokeOrder, ...redoStrokeOrder]);
  for (const token of activeTokens) {
    if (!stagedMirror.has(token)) {
      throw new Error(`Session stroke ${token} is missing from the worker mirror.`);
    }
  }
  for (const token of stagedMirror.keys()) {
    if (!activeTokens.has(token)) {
      stagedMirror.delete(token);
    }
  }

  const baseJson = JSON.stringify(base);
  const strokeBrushesJson = JSON.stringify(
    collectStrokeBrushSources(base, stagedMirror, strokeOrder, redoStrokeOrder)
  );
  const fieldsJson = [
    `"strokeBrushes":${strokeBrushesJson}`,
    `"strokes":[${strokeOrder.map((token) => stagedMirror.get(token).snapshotJson).join(",")}]`,
    `"redoStrokes":[${redoStrokeOrder.map((token) => stagedMirror.get(token).snapshotJson).join(",")}]`
  ].join(",");
  const json = baseJson === "{}"
    ? `{${fieldsJson}}`
    : `${baseJson.slice(0, -1)},${fieldsJson}}`;

  strokeMirror.clear();
  for (const [token, entry] of stagedMirror) {
    strokeMirror.set(token, entry);
  }
  return json;
}

self.addEventListener("message", (event) => {
  const message = event.data || {};
  const requestId = Number(message.requestId);
  if (!Number.isFinite(requestId)) {
    return;
  }

  try {
    const json = message.type === "serialize-incremental"
      ? serializeIncremental(message)
      : message.type === "serialize"
      ? JSON.stringify(message.snapshot)
      : null;
    if (typeof json !== "string") {
      return;
    }
    self.postMessage({ type: "serialized", requestId, json });
  } catch (error) {
    self.postMessage({
      type: "error",
      requestId,
      message: error instanceof Error ? error.message : "Session serialization failed."
    });
  }
});
