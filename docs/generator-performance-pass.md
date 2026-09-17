# Generator performance pass — 2026-09-17

Implemented without changing generation rules, effect timing, exported dimensions,
frame rates, or color quality. Existing workspace changes were preserved.

## Changes

- Batch pixelation animation/style reads before writing any canvas proxies; index
  composition specs once per composition instead of scanning them for every stamp.
- Retain bookmark cards, blob URLs, and decoded thumbnails during control changes;
  decode gallery images lazily. Preserve URLs across cancelled navigation/bfcache.
- Remove the redundant deep copy of all 30 history snapshots before each session
  save; IndexedDB already structured-clones the record synchronously on `put`.
- Coalesce resize requests without repeatedly cancelling the pending frame. Stop
  the pixelation scheduler while hidden and restart it on return; flush session
  persistence when the document becomes hidden.
- Track the active slider pointer, ignore competing pointers, and clean up on lost
  capture/cancellation. Remove duplicate range normalization during pointer moves.
- Move crop masking and uncropped-stamp alpha composition into the raster worker,
  preserving the previous per-channel rounding exactly. One completed RGBA frame
  returns for MP4 instead of two raw frames plus main-thread compositing.
- Encode WebP in the raster worker. Frames without cropping/overlays encode directly
  from its existing canvas; no RGBA readback/transfer or second encoding canvas.
  Cropped frames retain exact pixel processing before worker encoding. Reserve
  the additional processing frame before asset decoding to avoid late memory
  failures on constrained devices. Legacy worker callers keep their existing budget.
- Version generator assets and worker requests as `20260917-performance-v2`.

## Validation

Passed the generator, bookmark, WebP/MP4 export, export/lifecycle, and optimization
safety suites. Added `run-generator-performance-regression.mjs` for pointer
interruption, competing pointers, thumbnail identity, orientation changes, and
pixel-exact export comparison at 1200×800. It compared 19,200,000 RGBA bytes across
crop/no-crop, translucent uncropped stamps, all-uncropped, and direct lossless WebP
cases. Existing exports still pass timing, dimensions, codec/container, and
cancellation checks. The generator test helper also checks readiness and invokes
generation within one browser task, avoiding a race with queued slider updates.

Diagnostic stress run: 120 simultaneous pixelation effects, about 1.5 seconds per
sample. The control restores the old interleaved read/write ordering only; it is
not a comparison against the entire deployed application. Touch profiles use 4×
CPU throttling. Results are single-run diagnostics, not guaranteed device timings.

| Profile | Layouts, unbatched control → optimized | Style recalculations | P95 frame gap |
| --- | ---: | ---: | ---: |
| Desktop | 896 → 24 | 2106 → 197 | 89 → 83 ms |
| Surface-style, DPR 2 | 620 → 10 | 884 → 138 | 405 → 300 ms |
| Phone-size, DPR 3 | 595 → 9 | 894 → 144 | 448 → 271 ms |

The worst-case animation workload remains expensive; quality and animation
behavior have deliberately been preserved. Chromium CPU/touch/DPI emulation does
not validate Windows drivers, real Surface hardware, Firefox, or Safari.

The live URL returned HTTP 200 but still referenced `20260911-random-floor-v1`,
with `Cache-Control: max-age=600`, when inspected during this pass. The changes
in this workspace have not been deployed. Device comparison should use the same
revision, seed, controls, viewport, and browser after deployment.
