#!/usr/bin/env python3
"""Add concise visual captions for the representative frame of each brush."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import torch
from PIL import Image, ImageFile
from transformers import BlipForConditionalGeneration, BlipProcessor


ROOT = Path(__file__).resolve().parents[1]
MODEL_NAME = "Salesforce/blip-image-captioning-base"
Image.MAX_IMAGE_PIXELS = None
ImageFile.LOAD_TRUNCATED_IMAGES = True


def representative_frame(path: Path) -> Image.Image:
    with Image.open(path) as image:
        count = max(1, int(getattr(image, "n_frames", 1)))
        try:
            image.seek(count // 2)
        except EOFError:
            image.seek(0)
        frame = image.convert("RGBA")
        background = Image.new("RGBA", frame.size, "white")
        background.alpha_composite(frame)
        return background.convert("RGB")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=str(ROOT / ".brush-analysis-results.json"))
    parser.add_argument("--output", default=str(ROOT / ".brush-caption-results.json"))
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--batch-size", type=int, default=96)
    parser.add_argument("--max-new-tokens", type=int, default=10)
    args = parser.parse_args()

    payload = json.loads(Path(args.input).read_text())
    assets = payload["assets"][: args.limit or None]
    device = "mps" if torch.backends.mps.is_available() else "cpu"
    processor = BlipProcessor.from_pretrained(MODEL_NAME)
    model = BlipForConditionalGeneration.from_pretrained(
        MODEL_NAME, use_safetensors=True
    ).to(device).eval()
    if device == "mps":
        model = model.to(dtype=torch.float16)

    for start in range(0, len(assets), args.batch_size):
        batch_assets = assets[start : start + args.batch_size]
        images = []
        valid_assets = []
        for asset in batch_assets:
            try:
                images.append(representative_frame(ROOT / asset["source"]))
                valid_assets.append(asset)
            except Exception as error:
                asset["caption"] = ""
                asset["captionError"] = str(error)
        if images:
            inputs = processor(images=images, return_tensors="pt")
            inputs = {key: value.to(device) for key, value in inputs.items()}
            if device == "mps" and "pixel_values" in inputs:
                inputs["pixel_values"] = inputs["pixel_values"].to(dtype=torch.float16)
            with torch.inference_mode():
                generated = model.generate(
                    **inputs,
                    max_new_tokens=args.max_new_tokens,
                    num_beams=1,
                )
            captions = processor.batch_decode(generated, skip_special_tokens=True)
            for asset, caption in zip(valid_assets, captions):
                asset["caption"] = " ".join(caption.strip().split())
        if start % (args.batch_size * 5) == 0:
            print(f"captioned {min(start + len(batch_assets), len(assets))}/{len(assets)}", file=sys.stderr, flush=True)
            payload["captionModel"] = MODEL_NAME
            payload["assets"] = assets
            Path(args.output).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")

    payload["captionModel"] = MODEL_NAME
    payload["assets"] = assets
    Path(args.output).write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")
    print(f"wrote {len(assets)} captions to {args.output}", file=sys.stderr)


if __name__ == "__main__":
    main()
