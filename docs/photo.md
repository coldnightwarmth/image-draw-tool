# Photo collage builder

Serve the repository and open `/photo/`. Upload a still reference, then choose
stock samples, a local image folder, or both. Local references and samples stay
on the device; no image-upload service is involved. GIF samples animate while
the fitted positions stay fixed. Animated reference tracking is not supported.

The default is an overlapping collage. **Loose**, **balanced**, and **detailed**
are starting points for the sliders. Resemblance controls the scale of detail
being matched; increasing the image budget and lowering image size fills finer
features. Recolor and transparency are maximum allowances, not uniform effects
on every sample. The fitter can place fewer images than the budget when further
candidates would worsen the fit. **Grid mode** fixes centers and size to regular
cells and disables the free-placement controls.

**Reroll** changes the seed; **refine** preserves existing images and adds a pass
over remaining differences. Both buttons sit immediately to the left of pause
in the bottom action bar. **Stop** keeps the partial fit. **Show original**
temporarily overlays the reference for comparison. The seed and controls are
saved locally, but uploaded images and compositions are not restored on refresh.

PNG exports a still at the current preview time. WebP and MP4 start the animation
from the fitted representative frame of each sample and run for 1–15 seconds
(default 6). They use the generator's quality renderer: full source images,
lossless PNG/WebP, and the highest supported H.264 quality setting. WebP samples
at 50 fps and MP4 at 60 fps without stretching GIF timing. Export width defaults
to the reference width, capped at 1600 px; the export long side is capped at
2400 px. Odd MP4 dimensions are padded by at most one pixel for H.264.

The download location follows browser settings unless a folder is selected.
Folder selection requires the File System Access API (Chrome/Edge on supported
devices). Other browsers can use their “Ask where to save” download preference.
Existing files in a selected folder receive a numbered sibling, not an overwrite.
MP4 needs WebCodecs/H.264 encoding support; PNG and WebP remain available when
that encoder is unavailable. Missing network sources are skipped and reported.

## Rendering and limits

`photo/matcher.mjs` performs a seeded coarse-to-fine residual-error search. It
scores the actual alpha-composited result of a candidate image against a small
working reference, with controls for overlap, edge spill and reuse. Tint is fit
by least squares within the user's allowance. Output contains original sample
placements plus a flat background color; reference pixels are never an output
layer. Grid mode uses the same image scoring within fixed cells.

`photo/match-worker.js` keeps matching and sequential folder analysis off the UI
thread. A precomputed stock atlas represents each GIF using a visible frame
near its temporal color average. Preview and export load the original source
files. Preview caches frames at their on-screen sizes and may coalesce frames
to fit its memory budget; exports preserve the full-quality originals.
Repeated GIF uses share exact decoded frames and cached tinted rasters during
export, without changing paint order or pixels. A single canvas, one frame in
flight, bounded decoder memory, cancellable
workers and encoder backpressure prevent an unbounded stack of image layers or
queued frames. Preview pauses in hidden tabs. `[low fps]` appears when rendering
cannot maintain a smooth animated preview; offline export timing is independent
of preview speed. High budgets and large GIFs still take longer to animate/export.

Photo quality exports have a separate memory allowance for large source sets:
up to 2 GiB on devices reporting at least 8 GiB of RAM, 1 GiB on 4 GiB devices,
and 512 MiB on 2 GiB devices. Browsers without a memory estimate use 1 GiB.
These are ceilings, not up-front allocations. Preview is stopped during export,
and caches still evict under pressure. The live preview and existing generator
retain their previous memory policy. Very large individual sources or source
sets can still exceed the device's allowance.

The image budget is 25–8000 placements. Local imports accept GIF, PNG, JPEG and
WebP; each file is limited to 64 MB and 32 megapixels. Corrupt, transparent or
oversized samples are skipped. Worker canvas support is required. Tests include
Chromium desktop, phone layout and synthetic animation fixtures; they do not
establish performance on physical Surface hardware or mobile Safari.

## Rebuilding the stock index

After changing the stock library or `brush-metadata.js`, rebuild the index:

```sh
python3 -m pip install Pillow
python3 scripts/build_photo_index.py
```

Pillow is a development dependency only. This writes `photo/data/stock-index.json`
and `photo/data/stock-atlas.webp`; intermediate thumbnails are cached under the
ignored `node_modules/.photo-index-cache` directory. Commit both generated files
together. No private references are inputs to this script.

## Checks

```sh
node scripts/tests/run-photo-matcher-regression.mjs
node scripts/tests/run-raster-memory-budget-regression.mjs
npm install --no-save --package-lock=false playwright
npx playwright install chromium
node scripts/tests/run-photo-browser-regression.mjs
```

The browser suite starts an isolated server/context and tests local import,
unreadable-file handling, reconstruction, refinement, grid placement,
cancellation, PNG/WebP pixel equality, GIF timing, playable/seekable MP4, actual
downloads, and phone layout. Set `PHOTO_TEST_ARTIFACTS` to save screenshots and
fixture exports. `PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH` optionally selects an
existing Chromium binary. The user's three target images were also checked
locally at loose, balanced and detailed settings; they are not shipped here.
