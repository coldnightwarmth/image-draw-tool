# Scene render worker protocol

Create the worker as a module:

```js
const worker = new Worker("./scene-render-worker.js", { type: "module" });
```

Every request and response contains:

```js
{ protocol: "scene-render", version: 1, type: "..." }
```

`requestId` is optional and is repeated by direct acknowledgements and errors.

## Stamp record

A `scene` record and every `upsert` record is a complete object with this schema:

```js
{
  id: string | number,          // unique; numeric 1 and string "1" are distinct
  sourceUrl: string,
  sourceType: "auto" | "gif" | "static", // default: "auto"
  animated: boolean | null,     // source declaration; null when unknown
  mimeType: string,             // optional source hint

  centerX: number,              // world coordinates
  centerY: number,
  width: number,                // positive world dimensions
  height: number,
  rotation: number,             // clockwise degrees
  opacity: number,              // 0 through 1
  blendMode: "normal" | "multiply" | "screen" | "overlay" |
    "darken" | "lighten" | "color-dodge" | "color-burn" |
    "hard-light" | "soft-light" | "difference" | "exclusion" |
    "hue" | "saturation" | "color" | "luminosity",
  imageRendering: "pixelated" | "auto",
  visible: boolean,

  blurAmount: number,           // optional, 0..256 world pixels
  // Equivalent alternatives: filter: "blur(2px)" or
  // filter: { type: "blur", radius: 2 }. Other filters are rejected.

  startedAt: number,            // performance-timeline milliseconds
  phaseOffsetMs: number,        // optional additional per-stamp phase
  animationPaused: boolean,     // optional per-stamp freeze
  animationPausedAt: number     // required phase time when frozen
}
```

Use the canonical asset URL for `sourceUrl`, without per-stamp fragments or
cache-busting phase tokens. `startedAt` and `phaseOffsetMs` provide independent
playback while allowing every stamp to share one decoded source.

Missing `rotation`, `opacity`, `visible`, `phaseOffsetMs`, and animation-pause
fields receive neutral defaults. `startedAt` defaults to receipt time, but callers
should always send it to preserve independent GIF phase. Unsupported tint or
pixelate-effect fields with an active value produce capability errors instead of
being silently ignored. Conflicting `sourceType` or `animated` declarations for
the same URL are rejected; `animated: false` is a source assertion, not the
runtime pause control.

## Requests

### `init`

Transfer the canvas in the postMessage transfer list.

```js
{
  type: "init",
  canvas: OffscreenCanvas,
  width: number,              // CSS pixels
  height: number,
  dpr: number,
  timeOrigin?: performance.timeOrigin,
  now?: performance.now(),
  camera: { x: number, y: number, scale: number },
  options: {
    maxSourceBytes?: number,
    memoryBudgetBytes?: number,
    decodeConcurrency?: 1 | 2 | 3 | 4
  }
}
```

Response: `initialized`, including detected blend/filter capabilities. A failed
capability is returned as `error` with `error.capability: true`.

`memoryBudgetBytes` is enforced as a peak retained-bitmap budget, not only a
steady-state cache target. During a source LOD upgrade, the existing source
remains counted until the replacement has decoded successfully and the old
bitmaps are closed. Concurrent decodes are also counted through
`reservedBitmapBytes`.

Send `timeOrigin: performance.timeOrigin` (preferred) or `now:
performance.now()` so window-relative `startedAt` values are translated onto the
worker's performance timeline. Epoch-like `performance.timeOrigin +
performance.now()` stamp timestamps are also accepted directly.

### `scene`

```js
{ type: "scene", revision: nonNegativeInteger, records: StampRecord[] }
```

The array is the exact back-to-front draw order. `scene-ready` is emitted only
after every distinct referenced source has successfully reached `ready` and a
frame has been drawn. If any source fails, the response is `scene-error`; no
`scene-ready` is emitted for that revision.

### `upsert`

```js
{ type: "upsert", revision, record: StampRecord }
// or
{ type: "upsert", revision, records: StampRecord[] }
```

Existing records retain their order. New records append. The response is `ack`;
`presented: true` means the updated records have already been drawn. If a new
source must load first, the initial acknowledgement has `presented: false`,
source progress is emitted normally, and a `frame-presented` event covering the
current renderer revision is sent once every source used by the scene is ready
and the completed frame is drawn. Keeping a just-added DOM fallback
visible until either presentation response provides a flicker-free handoff.

### `remove`

```js
{ type: "remove", revision, id }
// or
{ type: "remove", revision, ids: Array<string | number> }
```

### `order`

```js
{ type: "order", revision, ids: Array<string | number> }
```

`ids` must list every current record exactly once in back-to-front order.

### `camera`

```js
{ type: "camera", camera: { x, y, scale } }
```

The mapping is `screen = world * scale + (x, y)` in CSS pixels.

### `resize`

```js
{ type: "resize", width, height, dpr }
```

### `pause`

```js
{ type: "pause", paused: boolean, now?: number }
```

Pausing freezes every GIF without collapsing independent `startedAt` phases.

### `dispose`

```js
{ type: "dispose" }
```

Closes every retained `ImageBitmap`, clears caches, replies `disposed`, and
closes the worker.

### `memory-stats`

```js
{ type: "memory-stats" }
```

Requests an immediate `memory-stats` event.

## Events and errors

- `source-status`: `loading`, `ready`, or `error` for one unique URL.
- `source-progress`: periodic GIF decode progress.
- `memory-stats`: source/frame/pixel counts, estimated bitmap bytes, fetched
  bytes, canvas and total estimated bytes, reservations, configured budget,
  LOD-limited source count, and stamp count.
- `ack`: successful delta/camera/resize/pause request.
- `frame-presented`: a delayed `upsert` has loaded its sources and been drawn.
- `error`: structured request/capability error.
- `scene-error`: one or more referenced sources failed for a full revision.

All errors contain `code`, `message`, `capability`, and `retriable`. Source and
record errors also include `sourceUrl` or `recordId` when applicable. Animated
PNG, animated WebP, animated SVG, AVIF sequences, and any non-GIF source declared
with `animated: true` fail with `UNSUPPORTED_ANIMATED_SOURCE`; they are never
rendered as a silent static first-frame substitute. Because arbitrary SVG can
contain external animation that byte sniffing cannot prove absent, an SVG must
use `sourceType: "static"` or have `animated: false`; otherwise it fails with
`AMBIGUOUS_ANIMATION_SUPPORT` and the caller can retain its compatibility path.

The concrete response envelopes are:

```js
{
  protocol: "scene-render", version: 1, type: "initialized",
  requestId?, width, height, dpr, camera,
  capabilities: {
    offscreenCanvas2d: true,
    moduleWorker: true,
    createImageBitmap: true,
    gif: true,
    animatedNonGif: false,
    blurFilter: boolean,
    blendModes: string[]
  },
  memoryBudgetBytes, decodeConcurrency,
  workerTimeOrigin, clientClockOffsetMs
}

{
  protocol: "scene-render", version: 1, type: "ack",
  action: "upsert" | "remove" | "order" | "camera" | "resize" | "pause",
  requestId?, revision,
  // Action-specific: recordIds?, removedCount?, width?, height?, dpr?, paused?,
  // upsert also reports presented: boolean,
  // or ignored: true plus reason: "stale-revision".
}

{
  protocol: "scene-render", version: 1, type: "frame-presented",
  action: "scene" | "upsert", requestId?, revision, recordIds?, reason?
}

{
  protocol: "scene-render", version: 1, type: "source-status",
  sourceUrl, status: "loading" | "ready" | "error", revision,
  source?: {
    kind: "gif" | "static", width, height, animated,
    originalFrameCount, storedFrameCount, totalDurationMs,
    targetWidth, targetHeight, spatialScale, targetFrameIntervalMs,
    estimatedBitmapBytes
  },
  error?: StructuredError
}

{
  protocol: "scene-render", version: 1, type: "source-progress",
  sourceUrl, decodedFrames, totalFrames
}

{
  protocol: "scene-render", version: 1, type: "scene-ready",
  requestId?, revision, sourceCount, stampCount, stats
}

{
  protocol: "scene-render", version: 1, type: "scene-error",
  requestId?, revision,
  errors: Array<{ sourceUrl: string, error: StructuredError }>
}

{
  protocol: "scene-render", version: 1, type: "memory-stats",
  reason: "update" | "source-ready" | "source-error" | "requested",
  stats: {
    sourceCount, loadingSourceCount, readySourceCount, failedSourceCount,
    gifSourceCount, staticSourceCount, originalFrameCount, storedFrameCount,
    bitmapPixels, estimatedBitmapBytes, canvasBytes, totalEstimatedBytes,
    fetchedBytes, memoryBudgetBytes, reservedBitmapBytes, stampCount,
    lodLimitedSourceCount
  }
}

{
  protocol: "scene-render", version: 1, type: "error",
  action, requestId?, revision?,
  error: StructuredError
}

// StructuredError
{
  code: string, message: string,
  capability: boolean, retriable: boolean,
  recordId?, sourceUrl?, details?
}

{
  protocol: "scene-render", version: 1, type: "disposed", requestId?
}
```
