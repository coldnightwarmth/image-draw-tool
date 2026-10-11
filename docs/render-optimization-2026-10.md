# Rendering optimization pass — 2026-10-11

This pass preserves the existing drawing/generator/photo controls, saved scene
schema, native and smooth preview choices, export options, output dimensions,
frame rates, GIF timing, effect math, and encoding quality. It removes repeated
work and bounds optional resources; it does not substitute lower-resolution
exports or an approximate color pipeline.

## Generator

- Retain each pixelation stamp's CSS animation handle instead of asking the
  browser to find it on every update. Invalidate on sequence changes and reacquire
  cancelled animations. Continue reading the browser's actual animation time.
- Write only properties affected by a scoped edit. Opacity edits, for example,
  leave position, dimensions, transforms, tint, and unrelated data attributes alone.
- Retain the smooth-preview worker and decoded GIFs across compatible edits.
  Rebuild when source identity, output geometry, requested decode dimensions, or
  initial-entry sampling requirements change. No lower-resolution cache is reused.
- Keep one frame in flight. Discard obsolete frames after an edit and render the
  latest scene. Preserve the animation timeline during compatible edits. Thumbnail
  and capture readiness follows the latest scene, including deferred sidebar edits
  that have reached preview scheduling; pending requests settle on cancellation.
- Refresh smooth preview after sequence-only edits as well as property edits.

A deterministic 300-sample fixture was run against the previous generator source
(commit `9c62926`) and the new source, in the same local Chromium installation.
The native fixture uses a fixed two-color uploaded image and paused pixelation;
its before/after 800×600 screenshots match pixel for pixel. The smooth fixture
uses 300 placements across 30 stock GIFs. These are focused measurements, not
whole-application FPS claims.

| Measurement | Before | After |
| --- | ---: | ---: |
| Native pixelation updater, median of 6 iterations | 333.5 ms | 3.1 ms |
| Animation-tree queries over those iterations | 1,800 | 0 after warmup |
| Stamp attribute mutations for one opacity edit | 3,900 | 900 |
| Smooth preview, edit to two completed frames | 1,132–1,182 ms | 214–267 ms |
| Worker creations / decoding preparations for 3 such edits | 3 / 3 | 0 / 0 |

The direct opacity-handler duration did not improve in this small sample
(19.8 ms before, 24.3 ms after); fewer downstream attribute invalidations and
avoided preview restarts are the measured benefits of that edit path. The
preview intentionally retains its existing sidebar interaction delay.

## Shared raster worker

Exact intermediate rasters can now be reused across stamps and frames. The key
includes asset identity, exact GIF frame, raster dimensions, sampling mode, and
all intermediate pixel-changing effects. Opacity, transform, blend mode, and blur
are still applied in the original paint order. Continuously changing effects
bypass cache admission. The optional cache uses at most 32 MiB or 1/16 of the job
budget; metadata is capped at 2,048 entries. Essential allocations can evict it.

Fully transparent stamps and provably off-canvas stamps skip decoding/effects.
Explicit blur halos are retained conservatively. Normal GIF frame selection uses
binary search over the same cumulative durations.

In the isolated 300-stamp benchmark, median time to rasterize nine frames:

| Fixture | Normal: before → after | Quality: before → after |
| --- | ---: | ---: |
| Repeated effects | 892 → 36 ms | 940 → 36 ms |
| Mostly off-canvas | 845 → 16 ms | 920 → 23 ms |
| Unique fixed effects with a small cache | 891 → 824 ms | 932 → 851 ms |
| Continuously changing effects | 759 → 774 ms | 829 → 862 ms |

The last case retains roughly 2–4% bookkeeping overhead; gains depend on reuse and
visibility. These are raster-stage figures, excluding encoding and downloads.
2,851,200 pixels matched the baseline exactly across alpha, color filters,
matrices, pixelation, blur, anisotropic transforms, crop overlays, 14 animated
frames, parameter edits, and forced optional-cache eviction.

## Drawing and photo

Drawing tints now share exact static SVG filters and reuse exclusively owned
animated filters. Removing stamps releases resources; undo and export restoration
retain the exact matrices. A 300-stamp/120-update test retained 300 filters instead
of 36,000. DOM tint-update time fell from 263.9 to 143.8 ms. Screenshot parity and
lifecycle details are in [drawing-tint-resources.md](drawing-tint-resources.md).

Photo matching retains the exact best 28 candidates without repeatedly allocating
and sorting the whole catalog. With all 3,049 stock assets, 1,000 ranking queries
fell from 613.5 to 113.4 ms (median of five alternating trials). A balanced fit at
224×187 working resolution and 600 attempted placements fell from 621.9 to
336.3 ms. 5,240 candidate comparisons and complete fit/refinement comparisons
returned identical choices, seeds, placements, errors, and pixels.

## Validation and limits

Focused checks cover preview reuse, one-frame backpressure, multiple edits while a
frame is held, thumbnail readiness, scale/pixelation decode invalidation,
inspection/native restoration, scoped settings, manual tint, mark inspection,
color/export parity, and resource cleanup. Actual encoded exports were decoded:
normal MP4 remains 30 fps, quality MP4 60 fps/QP 0, and quality WebP lossless at
50 frames per second. Photo import/refinement/export/cancellation and mobile layout
checks pass. The shared memory policy limits were not raised.

The controlled generator device/stability harnesses also passed desktop,
Surface-style high-DPI/touch/CPU-throttled, and phone-size checks, including
300-stamp one-frame backpressure, sidebar stability, injected failure/context
recovery, preview-mode persistence, and 19,200,000 RGBA-byte comparisons for
crop/overlay/WebP output. Realtime capture passed actual media playback, folder
output, smooth-preview recording, early finish, cancellation, and stream cleanup.
GIF decoder tests passed 151 frame comparisons with forced cache evictions.

These measurements use local macOS Chromium. Touch/DPR/CPU emulation can expose UI
problems but does not certify physical Surface/Windows GPU performance. Hundreds
of native GIF/CSS surfaces can still reach a browser/driver limit. This pass keeps
that default rendering choice intact and does not replace it with a new GPU engine.

The resource lifecycle follows the browser APIs' ownership requirements:
[CSSAnimation](https://developer.mozilla.org/en-US/docs/Web/API/CSSAnimation)
handles expose the current animation state, and bitmap frames drawn without
ownership transfer must be [closed after use](https://developer.mozilla.org/en-US/docs/Web/API/OffscreenCanvas/transferToImageBitmap).
