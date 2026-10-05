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
    quality: 100,
    method: 6,
    alpha_quality: 100
  });
  if (!result) throw new Error("Lossless WebP encoding failed.");
  return new Blob([result], { type: "image/webp" });
}
