#!/usr/bin/env python3
"""Losslessly optimize GIF assets, replacing only verified smaller results."""

from __future__ import annotations

import argparse
import concurrent.futures
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import threading

from PIL import Image, ImageChops


def animations_match(original_path: Path, candidate_path: Path) -> tuple[bool, str]:
    try:
        with Image.open(original_path) as original, Image.open(candidate_path) as candidate:
            original_frames = int(getattr(original, "n_frames", 1) or 1)
            candidate_frames = int(getattr(candidate, "n_frames", 1) or 1)
            if original.size != candidate.size:
                return False, "dimensions changed"
            if original_frames != candidate_frames:
                return False, "frame count changed"
            if original.info.get("loop") != candidate.info.get("loop"):
                return False, "loop count changed"

            for frame_index in range(original_frames):
                original.seek(frame_index)
                candidate.seek(frame_index)
                original_duration = int(original.info.get("duration") or 0)
                candidate_duration = int(candidate.info.get("duration") or 0)
                if original_duration != candidate_duration:
                    return False, f"frame {frame_index} timing changed"
                original_rgba = original.convert("RGBA")
                candidate_rgba = candidate.convert("RGBA")
                original_alpha = original_rgba.getchannel("A")
                candidate_alpha = candidate_rgba.getchannel("A")
                if ImageChops.difference(original_alpha, candidate_alpha).getbbox():
                    return False, f"frame {frame_index} alpha changed"
                rgb_difference = ImageChops.difference(
                    original_rgba.convert("RGB"),
                    candidate_rgba.convert("RGB"),
                )
                visible_mask = Image.merge(
                    "RGB",
                    (original_alpha, original_alpha, original_alpha),
                )
                if ImageChops.multiply(rgb_difference, visible_mask).getbbox():
                    return False, f"frame {frame_index} pixels or timing changed"
    except Exception as error:  # Pillow provides the independent decode check.
        return False, f"verification failed: {error}"
    return True, ""


def optimize_one(path: Path, gifsicle: str) -> tuple[str, int, int, str]:
    original_stat = path.stat()
    original_size = original_stat.st_size
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            prefix=f".{path.stem}-opt-",
            suffix=".gif",
            dir=path.parent,
            delete=False,
        ) as temporary:
            temporary_path = Path(temporary.name)

        result = subprocess.run(
            [
                gifsicle,
                "--optimize=3",
                "--careful",
                "--no-comments",
                "--no-names",
                str(path),
                "--output",
                str(temporary_path),
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            return "skipped", original_size, original_size, result.stderr.strip() or "gifsicle failed"

        candidate_size = temporary_path.stat().st_size
        if candidate_size >= original_size:
            return "unchanged", original_size, original_size, ""

        matches, reason = animations_match(path, temporary_path)
        if not matches:
            return "skipped", original_size, original_size, reason

        os.chmod(temporary_path, original_stat.st_mode)
        os.utime(
            temporary_path,
            ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns),
        )
        os.replace(temporary_path, path)
        temporary_path = None
        return "optimized", original_size, candidate_size, ""
    except Exception as error:
        return "skipped", original_size, original_size, str(error)
    finally:
        if temporary_path is not None:
            try:
                temporary_path.unlink()
            except FileNotFoundError:
                pass


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path, nargs="?", default=Path("brushes"))
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--verbose-skips", action="store_true")
    args = parser.parse_args()

    gifsicle = shutil.which("gifsicle")
    if not gifsicle:
        raise SystemExit("gifsicle is required")

    paths = sorted(
        (path for path in args.root.rglob("*") if path.is_file() and path.suffix.lower() == ".gif"),
        key=lambda path: path.stat().st_size,
        reverse=True,
    )
    totals = {"optimized": 0, "unchanged": 0, "skipped": 0}
    original_bytes = sum(path.stat().st_size for path in paths)
    final_bytes = original_bytes
    lock = threading.Lock()
    completed = 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.workers)) as executor:
        future_paths = {
            executor.submit(optimize_one, path, gifsicle): path
            for path in paths
        }
        for future in concurrent.futures.as_completed(future_paths):
            path = future_paths[future]
            status, before, after, reason = future.result()
            with lock:
                completed += 1
                totals[status] += 1
                final_bytes -= before - after
                if status == "skipped" and args.verbose_skips:
                    print(f"skip\t{path}\t{reason}", flush=True)
                if completed % 100 == 0 or completed == len(paths):
                    saved = original_bytes - final_bytes
                    print(
                        f"progress\t{completed}/{len(paths)}\toptimized={totals['optimized']}\t"
                        f"saved={saved}",
                        flush=True,
                    )

    print(
        f"done\tfiles={len(paths)}\toptimized={totals['optimized']}\t"
        f"unchanged={totals['unchanged']}\tskipped={totals['skipped']}\t"
        f"before={original_bytes}\tafter={final_bytes}\tsaved={original_bytes - final_bytes}"
    )
    return 0 if totals["skipped"] == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
