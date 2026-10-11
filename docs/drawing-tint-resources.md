# Drawing tint resource lifetime

The drawing page keeps the same sRGB SVG color matrices, layer order, alpha, grayscale,
and blur behavior. Matrices retain the existing six-decimal precision. Tint values are
not rounded into a smaller palette.

Previously, each distinct color/amount combination permanently added a filter to the
SVG definitions and a key to the cache. An animated color amount could therefore create
one resource per stamp per frame for the entire session.

The cache now holds resources referenced by connected elements. Identical tints share
one resource. When an element changes tint, an exclusively owned filter updates its
matrix in place; a shared filter splits without changing the other elements. Removing
or untinting the last owner releases the filter and cache entry. A weak element binding
retains the exact matrix needed for undo/reinsertion, without retaining removed DOM
through the global cache. Detached stamps acquire a live resource when inserted.

Sequence export snapshots also save exact tint matrices, because restoring an old CSS
URL alone would otherwise reuse the matrix most recently animated during export.

Run the browser regression with:

```sh
node scripts/tests/run-drawing-tint-resources-regression.mjs
```

It checks exact matrices, shared-resource isolation, tint removal, detached creation,
subtree cleanup, undo/reinsertion, export snapshot restoration, and byte-identical
browser screenshots against an immutable SVG filter. Its 300-stamp / 120-update stress
fixture retains 300 resources across 36,000 color updates and releases all of them when
removed.

For an isolated comparison against the original implementation:

```sh
node scripts/tests/benchmark-drawing-tint-resources.mjs 9c62926
```

This benchmark measures tint DOM update work and retained filter count, not overall
scene FPS. Set `PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH` to use a specific Chromium binary.

A local Chromium comparison on 2026-10-11 measured 36,000 exact color updates at
263.9 ms before and 143.8 ms after (about 45% less time), with retained filters falling
from 36,000 to 300. The test does not include rendering a whole animated composition;
its stable filter count, exact screenshot parity, and disposal checks are the primary
regression guarantees.
