#!/usr/bin/env python3
"""Read deterministic, render-safety metadata from a brush image asset."""

from __future__ import annotations

from pathlib import Path

from PIL import Image, ImageFile


Image.MAX_IMAGE_PIXELS = None
ImageFile.LOAD_TRUNCATED_IMAGES = True


def inspect_asset(path: Path) -> dict[str, int | bool]:
    """Return dimensions, animation timing, and conservative opacity data.

    ``opaque`` is true only when every decoded, composited frame covers the
    complete logical image with alpha 255. A frame decode failure makes it
    false, because callers use this value for render culling and a false
    negative is safe while a false positive is not.
    """

    with Image.open(path) as image:
        width, height = (int(value) for value in image.size)
        declared_count = max(1, int(getattr(image, "n_frames", 1)))
        duration_ms = 0
        opaque = True
        decoded_count = 0

        for index in range(declared_count):
            try:
                image.seek(index)
                duration = image.info.get("duration", 0)
                if isinstance(duration, (int, float)) and duration > 0:
                    duration_ms += round(duration)
                alpha_extrema = image.convert("RGBA").getchannel("A").getextrema()
                if alpha_extrema is None or int(alpha_extrema[0]) < 255:
                    opaque = False
                decoded_count += 1
            except (EOFError, OSError, ValueError):
                opaque = False
                break

        if decoded_count != declared_count:
            opaque = False

        return {
            "width": width,
            "height": height,
            "frameCount": declared_count,
            "durationMs": int(duration_ms),
            "animated": declared_count > 1,
            "opaque": opaque,
        }
