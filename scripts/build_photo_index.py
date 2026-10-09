#!/usr/bin/env python3
"""Build small, deterministic matching thumbnails without shipping GIF decodes.

Requires Pillow. Only stock assets are published; user references are never inputs.
Intermediate thumbnails live in ignored node_modules/.photo-index-cache.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path

from PIL import Image, ImageStat

ROOT = Path(__file__).resolve().parents[1]


def analyze(job):
    source, metadata, size = job
    path = ROOT / source
    stat = path.stat()
    key = hashlib.sha256(f"v2:{source}:{stat.st_size}:{stat.st_mtime_ns}:{size}".encode()).hexdigest()
    cache = ROOT / "node_modules/.photo-index-cache"
    cache.mkdir(parents=True, exist_ok=True)
    cached = cache / f"{key}.json"
    thumbnail = cache / f"{key}.png"
    if cached.exists() and thumbnail.exists():
        return json.loads(cached.read_text()), str(thumbnail)
    try:
        with Image.open(path) as image:
            width, height = image.size
            count = getattr(image, "n_frames", 1)
            sample_indices = set(round((count - 1) * fraction) for fraction in (0, .25, .5, .75, 1))
            samples = []
            elapsed = 0
            for index in range(count):
                image.seek(index)
                if index in sample_indices:
                    frame = image.convert("RGBA")
                    frame.thumbnail((size, size), Image.Resampling.LANCZOS)
                    tile = Image.new("RGBA", (size, size))
                    tile.paste(frame, ((size - frame.width) // 2, (size - frame.height) // 2))
                    averages = ImageStat.Stat(tile.convert("RGBa")).mean
                    coverage = averages[3] / 255
                    mean = [v / max(coverage, 1e-6) for v in averages[:3]]
                    samples.append((elapsed, tile, mean, coverage))
                elapsed += max(20, image.info.get("duration", 50) or 100)
            usable = [s for s in samples if s[3] > .008]
            if not usable:
                return None
            mean = [sum(s[2][c] * s[3] for s in usable) / sum(s[3] for s in usable) for c in range(3)]
            # Prefer a visible real frame whose colors represent the animation.
            phase, tile, color, coverage = min(usable, key=lambda s: sum((s[2][c] - mean[c]) ** 2 for c in range(3)) + (1 - s[3]) * 120)
            entry = {"source": source, "name": metadata.get("name", path.stem),
                     "category": path.parent.name, "width": width, "height": height,
                     "frames": count, "duration": elapsed if count > 1 else 0,
                     "phase": phase, "mean": [round(v, 2) for v in color],
                     "temporalMean": [round(v, 2) for v in mean], "coverage": round(coverage, 5)}
            tile.save(thumbnail)
            cached.write_text(json.dumps(entry))
            return entry, str(thumbnail)
    except Exception as error:
        print(f"Skipping {source}: {error}", flush=True)
        return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--size", type=int, default=32)
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()
    text = (ROOT / "brush-metadata.js").read_text()
    metadata = json.loads(text.split("window.STOCK_BRUSH_METADATA =", 1)[1].strip().removesuffix(";"))
    jobs = [(source, info, args.size) for source, info in sorted(metadata.items()) if (ROOT / source).exists()]
    if args.limit:
        jobs = jobs[:args.limit]
    results = []
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for index, result in enumerate(pool.map(analyze, jobs)):
            if result:
                results.append(result)
            if (index + 1) % 100 == 0:
                print(f"Indexed {index + 1}/{len(jobs)}", flush=True)
    columns = 64
    atlas = Image.new("RGBA", (columns * args.size, ((len(results) + columns - 1) // columns) * args.size))
    for index, (_, tile) in enumerate(results):
        with Image.open(tile) as image:
            atlas.paste(image, ((index % columns) * args.size, (index // columns) * args.size))
    destination = ROOT / "photo/data"
    destination.mkdir(parents=True, exist_ok=True)
    atlas.save(destination / "stock-atlas.webp", lossless=True, method=4, exact=True)
    manifest = {"version": 1, "tileSize": args.size, "columns": columns,
                "atlas": "stock-atlas.webp", "assets": [entry for entry, _ in results]}
    (destination / "stock-index.json").write_text(json.dumps(manifest, separators=(",", ":")) + "\n")
    print(f"Saved {len(results)} assets; atlas {(destination / 'stock-atlas.webp').stat().st_size:,} bytes", flush=True)


if __name__ == "__main__":
    main()
