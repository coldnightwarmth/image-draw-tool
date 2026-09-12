# Drawing performance/regression harness

This harness exercises the app through its existing controls and pointer handlers. It does not import or reach into `app.js` state, and the automated runner uses a fresh browser context so it cannot overwrite a normal drawing session.

The dependency-free focused regression test for animated export crop membership and unload-time session persistence is run separately:

```sh
node scripts/test_export_and_lifecycle_regressions.mjs
```

The finite-canvas composition generator has its own browser regression run:

```sh
node scripts/tests/run-generator-regression.mjs
node scripts/tests/run-generator-bookmark-regression.mjs
node scripts/tests/run-generator-export-regression.mjs
```

It verifies the clean `/generator/` route, the complete ALL catalog, exact and
distinct placement counts, line/spray/box/scatter generation, fixed-property
controls, independent category/tag filtering, deterministic sequence effects,
explicit min/max randomization ranges, opt-in seeded rerolls for GIF count,
strongly lower-biased margin amounts with an extra compact-margin preference,
randomized margin behavior, enabled sequence effects, and range endpoints, the
manual 1–4 GIF range, hard five-GIF randomized floor, strongly lower-biased
300-GIF new-composition ceiling, full-gamut seeded backgrounds, finite bounds,
placement margins, foreground crop margins, paused crop inspection,
per-stamp uncropped exceptions, live/export pixel-grid parity for the pixelate
sequence effect, active composition/settings restoration after
refresh, live same-seed control updates with stable GIF assignments,
in-place sequence-only updates that retain every GIF node and all unrelated
visual properties, background-only rerolls, the persisted 30-action undo history, the 500-item
local bookmark gallery and its alternate sidebar view, persistent-storage enrollment,
portable bookmark backup/restore,
and browser console errors. The dedicated export run
decodes animated sources, exports image-cycle and blur compositions at the
canvas's exact pixel dimensions, and checks that selected stamps can render
above the crop. It validates the animated RIFF/WebP frame structure, lossless
VP8L color, auto-loop timing, and cancellation. It also validates the split
download control's six-second, 30fps H.264 MP4 at the canvas's full dimensions,
including its playable duration and AVC container metadata. The generator reuses
the production animation raster pipeline for both formats, then packages
full-color WebP frames without GIF palette quantization or streams those frames
through the browser's native H.264 encoder for MP4.

That focused test also verifies large-scene session saves use one immediate
leading write plus a non-starving, fixed-deadline trailing throttle during
continuous slider/input activity.

It covers:

- deterministic high-count stamp generation with a static PNG brush and trusted mouse input;
- one-step undo/redo, including preservation of stamp node identity, geometry, and order;
- viewport culling after a large middle-button pan and source restoration after panning back;
- the demand-driven layer-sequence scheduler when no effect is configured, enabled, and disabled;
- adaptive sequence cadence for large offscreen layers, bounded Pulse/Bounce catch-up, Bounce runtime rebasing after a layer-size change, and zero no-op stamp class churn while a sequence is active;
- sequence pause/resume when the page becomes hidden and visible (supported Chromium modes);
- immediate large-scene reload recovery with a forced session-storage quota failure and IndexedDB lifecycle handoff;
- long-task entries, animation-frame gaps, resource bytes, JS heap data when Chromium exposes it, and DOM/stamp counts per phase.

## Automated Chromium run

The runner has no project runtime dependency. Install Playwright without saving it to this repo, then install Chromium once:

```sh
npm install --no-save --package-lock=false playwright
npx playwright install chromium
node scripts/tests/run-performance-regression.mjs --stamps 2000
```

The script serves the repository on an ephemeral localhost port by default. To test an already-running instance:

```sh
node scripts/tests/run-performance-regression.mjs \
  --url http://127.0.0.1:4177/ \
  --stamps 5000 \
  --output /tmp/drawing-performance.json
```

Useful options:

```text
--headful
--brush-file /absolute/path/to/static-image.png
--viewport 1280x800
--pointer-move-steps 4
--max-long-task-ms 250
--max-p95-frame-gap-ms 50
```

Functional regressions and uncaught page errors always produce exit code 1. Performance varies by device, so timing limits are opt-in. A headless browser may keep every page `visible`; in that case the visibility assertion is explicitly reported as skipped. Use `--headful` to exercise real tab backgrounding when needed.

## Dependency-free browser-console run

Serve the repository, open the app in a new/private tab, paste `browser-performance-harness.js` into DevTools, then run:

```js
const report = await DrawingPerfHarness.run({
  targetStampCount: 1000,
  cleanup: true
});
console.log(report);
```

The console fallback uses synthetic pointer events because DevTools cannot create trusted input or background its own page. It still passes through the app's normal pointer and UI event handlers, and it reports the visibility check as skipped. Prefer a new/private tab: drawing a test stroke intentionally clears the app's redo stack, even though `cleanup: true` undoes the generated stroke afterward.

## Interpreting reports

`functional` contains pass/fail details and before/after scene snapshots for each invariant. `phases` isolates generation, history, culling, sequencing, and visibility timings. `telemetry.frames` reports frame-gap percentiles and counts over 32/50/100 ms; `telemetry.longTasks` contains every browser long-task entry plus aggregate duration.

For device-to-device comparisons, keep the stamp count, viewport, pointer-move steps, browser version, and headless/headful setting identical.
