# Drawing performance/regression harness

This harness exercises the app through its existing controls and pointer handlers. It does not import or reach into `app.js` state, and the automated runner uses a fresh browser context so it cannot overwrite a normal drawing session.

The dependency-free focused regression test for animated export crop membership and unload-time session persistence is run separately:

```sh
node scripts/test_export_and_lifecycle_regressions.mjs
```

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
