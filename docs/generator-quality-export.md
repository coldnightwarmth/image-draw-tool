# Generator quality rendering

The export popup offers **normal**, **realtime**, and **quality**, in that order.
Normal remains the default. Quality works with MP4, WebP, and the bookmark queue;
its filenames are distinct from normal/realtime exports.

Quality is an offline render, independent of preview performance or screen size.
It uses the requested canvas resolution, original source GIF dimensions and all
native GIF frame timings. A bounded LRU reuses exact native-resolution frames
across stamps, timestamps and phase offsets. Saved frames also retain disposal
state so a rewind can start at the closest valid checkpoint. Full opaque frames
without restore-previous disposal provide independent seek points in long GIFs.
Under memory pressure, cached frames and compositors are evicted and reconstructed
rather than downsampling or dropping source animation frames. Optional frame
caches use at most 40% of the existing worker budget and yield to required output
and decoding storage. An individual source/output that cannot fit still fails
clearly rather than silently reducing quality. Larger or busier scenes take longer.

MP4 renders effects at 60 fps and prefers H.264 High profile and software encoding.
It negotiates minimum per-frame quantization (QP 0) where the browser supports
quantizer mode. Otherwise its variable bitrate target is 4 bits per pixel per
frame, with a 64 Mbps floor and a 300 Mbps High-profile ceiling (240 Mbps for
Main/Baseline): 230.4 Mbps at the default 1200×800 canvas, versus
5.184 Mbps in normal mode. It encodes directly from rendered frames, without a
screen recording or intermediate lossy video. Blob-backed muxer chunks preserve
header patches and standard seekable MP4 output without a second contiguous copy
of the entire encoded video. Browser codec support still varies; H.264 color
conversion can lose detail even at QP 0, so this is not advertised as lossless.

WebP renders at 50 fps (20 ms frame delays) and uses the bundled libwebp encoder
with lossless/exact mode, full alpha quality and fastest lossless compression
effort (`quality: 0`, `method: 0`, `near_lossless: 100`). In lossless mode those
effort settings affect file size and encoding time, not image fidelity; see the
[WebP API documentation](https://developers.google.com/speed/webp/docs/api).
It preserves the final composited RGBA pixels, independent of the browser's canvas
WebP quality behavior.
It reuses the previous compressed frame only when all RGBA pixels and dimensions
match exactly, retaining every output frame and delay. The encoder keeps one owned
comparison frame and clears it on job release. It also consumes the existing
composited readback directly instead of copying through another canvas read/write.
It is the option for an image-quality master. Both formats can produce much larger
files than normal mode. The normal/realtime settings and generation rules remain
unchanged.

Quality worker scheduling uses elapsed work time (8 ms slices) rather than a
fixed pause every eight stamps. Scheduler yields, with a MessageChannel fallback,
allow cancellation and progress without nested timer clamping. Normal/realtime
rendering and MP4 codec, bitrate, quantizer, frame rate and dimensions are unchanged.

Regression commands:

```sh
node scripts/tests/run-quality-gif-decoder-regression.mjs
node scripts/tests/run-generator-quality-regression.mjs
node scripts/tests/run-generator-export-regression.mjs
node scripts/tests/run-generator-batch-export-regression.mjs
```

The decoder test compares native browser GIF pixels across disposal modes 2/3,
rewinds, looping, forced compositor/snapshot eviction and cancellation. It also
checks exact frame reuse and independent seeks through a 204-frame GIF, including
dependent frames that must not be treated as seek points. The quality export test
uses 300 animated/effected layers, checks encoded MP4 timing and seeking, compares
compression error against normal exports, verifies lossless WebP pixels, and
checks mobile layout and cancellation. The batch suite includes quality output
and duplicate-file skips. Set `QUALITY_FORCE_MESSAGE_CHANNEL=1` on the quality
test to exercise the worker scheduling fallback. Browser tests use Chromium;
physical Surface hardware and other browsers are not covered by these automated checks.

For reproducible speed measurements, run `scripts/tests/run-generator-quality-benchmark.mjs`.
The default case exports a one-second 320×320 composition with 300 rotated GIF
layers and crop overlays. `QUALITY_BENCHMARK_CASE=large` uses a 1200×800 canvas,
300 layers and 32 source GIFs; `still` uses four static layers at 1200×800.
`QUALITY_BENCHMARK_FORMATS=mp4` limits the formats. For a before/after comparison,
`QUALITY_BASELINE_DIR=/absolute/path/to/snapshot` serves matching implementation
files from that directory, falling back to the working tree for other assets.
Run comparisons sequentially on the same idle device. The script checks that all
sources loaded and emits exact raster hashes in addition to timings and file sizes.

On the development Mac with headless Chromium (October 5, 2026), one-second export
measurements against `980ff97` were:

| Fixture | Before | After |
| --- | ---: | ---: |
| 320×320, 300 layers, MP4 | 21.2 s | 0.88 s |
| 320×320, 300 layers, WebP | 79.3 s | 0.98 s |
| 1200×800, 300 layers / 32 GIF sources, MP4 | 24.9 s | 3.81 s |

Five sampled source raster hashes matched the baseline exactly in both animated
fixtures. The faster WebP compression produced 4,454,572 bytes instead of 508,132
bytes in the small/busy fixture; decoded pixels remained exact. Speedups and file
sizes depend on the composition and device. After the first two optimizations,
the additional identical-frame reuse/readback change cut the still WebP fixture
from 2.07 s to 0.90 s, with the same encoded bytes.
