const MEBIBYTE = 1024 * 1024;
export const PHOTO_EXPORT_MEMORY_PROFILE = "photo-export";
export const MAX_PHOTO_EXPORT_MEMORY_BYTES = 2048 * MEBIBYTE;

// Photo exports may retain hundreds of distinct compressed GIFs even after
// evicting every decoded frame. Give that offline job more room while keeping
// the live preview and existing drawing/generator policy at their usual limits.
export function resolveRasterMemoryBudget(requestedBytes, { deviceMemoryGiB, profile } = {}) {
  const photo = profile === PHOTO_EXPORT_MEMORY_PROFILE;
  const maximum = photo ? MAX_PHOTO_EXPORT_MEMORY_BYTES : 768 * MEBIBYTE;
  const minimum = (photo ? 256 : 64) * MEBIBYTE;
  const fallback = (photo ? 1024 : 384) * MEBIBYTE;
  const memory = Number(deviceMemoryGiB);
  const detected = Number.isFinite(memory) && memory > 0
    ? memory * (photo ? 256 : 96) * MEBIBYTE
    : fallback;
  const automatic = Math.min(maximum, Math.max(minimum, Math.round(detected)));
  const requested = Number(requestedBytes);
  return !Number.isFinite(requested) || requested <= 0
    ? automatic
    : Math.min(automatic, Math.max(32 * MEBIBYTE, Math.min(maximum, Math.round(requested))));
}
