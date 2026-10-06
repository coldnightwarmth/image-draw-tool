import createEncoder from "./vendor/webp/webp_enc.js";
import { defaultOptions } from "./vendor/webp/meta.js";

let encoder;

// Local libwebp, rather than browser-dependent canvas quality semantics.
export async function encodeLosslessWebp(image) {
  encoder ||= createEncoder({ noInitialRun: true });
  const module = await encoder;
  const result = module.encode(image.data, image.width, image.height, {
    ...defaultOptions,
    lossless: 1,
    near_lossless: 100,
    exact: 1,
    // In lossless mode these control compression effort/file size, not pixels.
    // Avoid expensive entropy searches for every frame of an animation.
    quality: 0,
    method: 0,
    alpha_quality: 100
  });
  if (!result) throw new Error("Lossless WebP encoding failed.");
  return new Blob([result], { type: "image/webp" });
}

export function createLosslessWebpEncoder() {
  let previous = null;
  return {
    async encode(image) {
      const pixels = image.data.byteOffset % 4 === 0
        ? new Uint32Array(image.data.buffer, image.data.byteOffset, image.data.byteLength / 4)
        : new Uint32Array(image.data.slice().buffer);
      if (previous?.width === image.width && previous.height === image.height) {
        let index = 0;
        while (index < pixels.length && pixels[index] === previous.pixels[index]) index++;
        if (index === pixels.length) return previous.blob;
      }
      const blob = await encodeLosslessWebp(image);
      // Own one exact RGBA copy: callers may reuse or transfer their readback.
      // Reuse compression only, preserving every animation frame and its delay.
      const saved = previous?.pixels.length === pixels.length ? previous.pixels : new Uint32Array(pixels.length);
      saved.set(pixels);
      previous = { width: image.width, height: image.height, pixels: saved, blob };
      return blob;
    },
    clear() { previous = null; }
  };
}
