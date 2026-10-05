# Generator quality rendering

The export popup offers **normal**, **realtime**, and **quality**, in that order.
Normal remains the default. Quality works with MP4, WebP, and the bookmark queue;
its filenames are distinct from normal/realtime exports.

Quality is an offline render, independent of preview performance or screen size.
It uses the requested canvas resolution, original source GIF dimensions and all
native GIF frame timings. A bounded LRU of GIF compositors reconstructs frames
on demand, preserving transparency, disposal and phase offsets. Under memory
pressure, compositors are evicted and reconstructed rather than downsampling or
dropping source frames. An individual source/output that cannot fit still fails
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
with lossless/exact mode, full alpha quality and method 6. It preserves the final
composited RGBA pixels, independent of the browser's canvas WebP quality behavior.
It is the option for an image-quality master. Both formats can produce much larger
files than normal mode. The normal/realtime settings and generation rules remain
unchanged.

Regression commands:

```sh
node scripts/tests/run-quality-gif-decoder-regression.mjs
node scripts/tests/run-generator-quality-regression.mjs
node scripts/tests/run-generator-export-regression.mjs
node scripts/tests/run-generator-batch-export-regression.mjs
```

The decoder test compares native browser GIF pixels across disposal modes 2/3,
rewinds, looping, forced cache eviction and cancellation. The quality export test
uses 300 animated/effected layers, checks encoded MP4 timing and seeking, compares
compression error against normal exports, verifies lossless WebP pixels, and
checks mobile layout and cancellation. The batch suite includes quality output
and duplicate-file skips. Browser tests use Chromium; physical Surface hardware
and other browsers are not covered by these automated checks.
