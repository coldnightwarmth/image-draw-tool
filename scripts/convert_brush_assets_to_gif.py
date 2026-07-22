#!/usr/bin/env python3
"""Convert every non-GIF image in brush data to an animated GIF counterpart.

Source files are retained as legacy compatibility assets. The brush catalog can
then point at the generated .gif files while older saved scenes keep resolving.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from PIL import Image

from optimize_gifs_losslessly import animations_match


ROOT = Path(__file__).resolve().parents[1]
BRUSHES_ROOT = ROOT / "brushes"
SUPPORTED_SOURCE_EXTENSIONS = {
    ".apng",
    ".avif",
    ".bmp",
    ".jpeg",
    ".jpg",
    ".png",
    ".tif",
    ".tiff",
    ".webp",
}


def read_webp_durations(path: Path) -> list[int]:
    """Read ANMF durations because Pillow omits the first WebP frame delay."""
    data = path.read_bytes()
    if len(data) < 12 or data[:4] != b"RIFF" or data[8:12] != b"WEBP":
        return []
    durations: list[int] = []
    offset = 12
    while offset + 8 <= len(data):
        chunk_type = data[offset : offset + 4]
        chunk_size = int.from_bytes(data[offset + 4 : offset + 8], "little")
        chunk = data[offset + 8 : offset + 8 + chunk_size]
        if chunk_type == b"ANMF" and len(chunk) >= 16:
            durations.append(int.from_bytes(chunk[12:15], "little"))
        offset += 8 + chunk_size + (chunk_size & 1)
    return durations


def gif_compatible_durations(durations: list[float]) -> list[int]:
    """Round cumulatively so GIF's 10 ms clock preserves the total duration."""
    output: list[int] = []
    source_total = 0.0
    encoded_total = 0
    for duration in durations:
        source_total += max(20.0, float(duration or 100.0))
        target_total = max(encoded_total + 20, int(round(source_total / 10.0)) * 10)
        output.append(target_total - encoded_total)
        encoded_total = target_total
    return output


def quantize_rgba_frame(frame: Image.Image) -> Image.Image:
    rgba = frame.convert("RGBA")
    alpha = rgba.getchannel("A")
    rgb = rgba.convert("RGB")
    fully_transparent = alpha.point(lambda value: 255 if value == 0 else 0)
    rgb.paste((0, 0, 0), mask=fully_transparent)
    paletted = rgb.quantize(
        colors=255,
        method=Image.Quantize.MEDIANCUT,
        dither=Image.Dither.FLOYDSTEINBERG,
    )
    palette = list(paletted.getpalette() or [])[: 255 * 3]
    palette.extend([0] * (255 * 3 - len(palette)))
    palette.extend([0, 0, 0])
    paletted.putpalette(palette)
    transparency_mask = alpha.point(lambda value: 255 if value < 128 else 0)
    paletted.paste(255, mask=transparency_mask)
    paletted.info["transparency"] = 255
    paletted.info["disposal"] = 2
    return paletted


def target_size(path: Path, source_size: tuple[int, int], nu_max_dimension: int) -> tuple[int, int]:
    relative = path.relative_to(BRUSHES_ROOT)
    width, height = source_size
    if relative.parts[0].casefold() != "nu" or max(width, height) <= nu_max_dimension:
        return width, height
    scale = nu_max_dimension / max(width, height)
    return max(1, round(width * scale)), max(1, round(height * scale))


def save_converted_gif(source: Path, temporary_path: Path, nu_max_dimension: int) -> None:
    with Image.open(source) as image:
        frame_count = int(getattr(image, "n_frames", 1) or 1)
        webp_durations = read_webp_durations(source) if image.format == "WEBP" else []
        frames: list[Image.Image] = []
        durations: list[float] = []
        output_size = target_size(source, image.size, nu_max_dimension)
        loop = max(0, min(65535, int(image.info.get("loop") or 0)))

        for frame_index in range(frame_count):
            image.seek(frame_index)
            rgba = image.convert("RGBA")
            if rgba.size != output_size:
                rgba = rgba.resize(output_size, Image.Resampling.LANCZOS)
            frames.append(quantize_rgba_frame(rgba))
            if frame_index < len(webp_durations):
                durations.append(float(webp_durations[frame_index]))
            else:
                durations.append(float(image.info.get("duration") or 100.0))

    encoded_durations = gif_compatible_durations(durations)
    frames[0].save(
        temporary_path,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=encoded_durations,
        loop=loop,
        disposal=2,
        transparency=255,
        optimize=False,
    )


def optimize_candidate(path: Path, gifsicle: str | None) -> None:
    if not gifsicle:
        return
    with tempfile.NamedTemporaryFile(
        prefix=f".{path.stem}-optimized-",
        suffix=".gif",
        dir=path.parent,
        delete=False,
    ) as temporary:
        optimized_path = Path(temporary.name)
    try:
        result = subprocess.run(
            [
                gifsicle,
                "--optimize=3",
                "--careful",
                "--no-comments",
                "--no-names",
                str(path),
                "--output",
                str(optimized_path),
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if result.returncode != 0 or optimized_path.stat().st_size >= path.stat().st_size:
            return
        matches, _ = animations_match(path, optimized_path)
        if matches:
            os.replace(optimized_path, path)
            optimized_path = None
    finally:
        if optimized_path is not None:
            optimized_path.unlink(missing_ok=True)


def convert_one(
    source: Path,
    nu_max_dimension: int,
    gifsicle: str | None,
    force: bool,
) -> tuple[Path, int, int, bool]:
    destination = source.with_suffix(".gif")
    if destination.exists() and not force:
        with Image.open(destination) as converted:
            frame_count = int(getattr(converted, "n_frames", 1) or 1)
        return destination, destination.stat().st_size, frame_count, False
    with tempfile.NamedTemporaryFile(
        prefix=f".{destination.stem}-converted-",
        suffix=".gif",
        dir=destination.parent,
        delete=False,
    ) as temporary:
        temporary_path = Path(temporary.name)
    try:
        with Image.open(source) as image:
            source_is_gif = image.format == "GIF"
        if source_is_gif:
            shutil.copyfile(source, temporary_path)
        else:
            save_converted_gif(source, temporary_path, nu_max_dimension)
        optimize_candidate(temporary_path, gifsicle)
        with Image.open(temporary_path) as converted:
            converted.load()
            frame_count = int(getattr(converted, "n_frames", 1) or 1)
        os.replace(temporary_path, destination)
        temporary_path = None
        return destination, destination.stat().st_size, frame_count, True
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path, nargs="?", default=BRUSHES_ROOT)
    parser.add_argument("--nu-max-dimension", type=int, default=300)
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()

    sources = sorted(
        path
        for path in args.root.rglob("*")
        if path.is_file() and path.suffix.casefold() in SUPPORTED_SOURCE_EXTENSIONS
    )
    gifsicle = shutil.which("gifsicle")
    print(f"converting {len(sources)} non-GIF brush assets")
    for source in sources:
        destination, size, frame_count, converted = convert_one(
            source,
            max(1, args.nu_max_dimension),
            gifsicle,
            args.force,
        )
        status = "converted" if converted else "already converted"
        print(f"{status}\t{source.relative_to(ROOT)}\t{destination.relative_to(ROOT)}\t{size}\t{frame_count} frames")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
