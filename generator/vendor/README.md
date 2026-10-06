# Generator export dependency

`mp4-muxer.mjs` is the browser ESM build of
[`mp4-muxer` 5.2.2](https://www.npmjs.com/package/mp4-muxer/v/5.2.2). It packages
the generator's native WebCodecs H.264 stream into an MP4 without a network or
runtime package dependency. Its MIT license is preserved in
`mp4-muxer.LICENSE`.

`webp/` contains the non-SIMD encoder and option defaults from
[`@jsquash/webp` 1.5.0](https://github.com/jamsinclair/jSquash/tree/main/packages/webp).
Only quality WebP exports load this local WebAssembly encoder. There is no CDN
or runtime package dependency. The wrapper explicitly enables lossless mode,
exact pixels, full alpha quality, and fastest lossless compression effort.
Lossless effort affects encoding time and file size; it does not lower pixel
quality. See [WebP's configuration reference](https://developers.google.com/speed/webp/docs/api).

Source archive: `https://registry.npmjs.org/@jsquash/webp/-/webp-1.5.0.tgz`
with npm SHA-512 integrity
`KggLoj2MnRSfIqTeKe1EmbljTX2vuV7mh79k89PCL1pyqiDULcPM1L47twxXt0hkb68F70bXiL31MxsuoZtKFw==`.
Upstream files are unmodified; Apache and codec licenses are retained in
`webp/LICENSE` and `webp/LICENSE.codec.md`.
