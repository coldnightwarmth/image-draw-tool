#!/usr/bin/env python3
"""Analyze stock brush images and emit site-facing names/tags without renaming assets.

This script uses CLIP for semantic/style scoring and combines those scores with
animation geometry, transparency, filenames, and the curated source grouping.
It is intentionally deterministic so the generated metadata can be audited and
reproduced when the stock catalog changes.
"""

from __future__ import annotations

import argparse
import collections
import json
import math
import re
import subprocess
import sys
import unicodedata
from pathlib import Path

import numpy as np
import torch
from PIL import Image, ImageFile
from transformers import CLIPModel, CLIPProcessor

from brush_asset_info import inspect_asset


ROOT = Path(__file__).resolve().parents[1]
MODEL_NAME = "openai/clip-vit-base-patch32"
ALLOWED_TAGS = (
    "plant", "flower", "animal", "character", "anime", "pixel-art",
    "glitch", "3d", "video-game", "cartoon", "illustration",
    "live-action", "abstract", "text", "framing", "particle",
    "lighting", "box", "cute", "spiritual", "western", "meme", "misc",
)

TAG_PROMPTS = {
    "plant": "a plant, leaf, tree, vine, mushroom, or other botanical subject",
    "flower": "a flower, blossom, rose, daisy, sunflower, or floral subject",
    "animal": "an animal, bird, fish, insect, mammal, reptile, or creature",
    "character": "a person, face, human figure, mascot, or fictional character",
    "anime": "Japanese anime or manga artwork and anime characters",
    "pixel-art": "low-resolution pixel art, sprite art, or retro computer graphics",
    "glitch": "glitch art, corrupted pixels, digital distortion, or datamoshing",
    "3d": "a three-dimensional rendered object or CGI animation",
    "video-game": "video game footage, a game sprite, game interface, or arcade graphic",
    "cartoon": "a cartoon, comic, animated drawing, or mascot illustration",
    "illustration": "a drawing, painting, graphic illustration, or decorative artwork",
    "live-action": "a photograph or live-action camera recording of the real world",
    "abstract": "an abstract pattern, geometric shape, swirl, texture, or visual effect",
    "text": "written words, lettering, typography, a caption, logo, or sign",
    "framing": "a decorative border, frame, divider, corner, or edge ornament",
    "particle": "particles, sparks, bubbles, confetti, snow, dust, or floating dots",
    "lighting": "a luminous glow, beam, flash, flame, lightning, neon, or light effect",
    "box": "a full rectangular image or uncropped footage filling the image edges",
    "cute": "a cute, sweet, charming, adorable, or kawaii subject",
    "spiritual": "religious, sacred, mystical, occult, angelic, or spiritual symbolism",
    "western": "cowboys, the American old west, western film, desert, or frontier imagery",
    "meme": "a reaction image, internet meme, humorous caption, or viral pop-culture clip",
    "misc": "an unusual miscellaneous object or subject with no clear category",
}

CONCEPTS = (
    "flower", "rose", "sunflower", "bouquet", "leaf", "plant", "tree", "palm tree",
    "mushroom", "fruit", "butterfly", "bird", "cat", "dog", "horse", "fish", "frog",
    "rabbit", "bear", "insect", "dragon", "dinosaur", "animal", "anime girl",
    "anime boy", "woman", "man", "child", "baby", "dancer", "face", "eye", "hand",
    "character", "angel", "demon", "ghost", "skull", "wizard", "cowboy", "heart",
    "star", "sun", "moon", "planet", "cloud", "fire", "flame", "smoke", "water",
    "lightning", "rainbow", "sparkles", "explosion", "bubbles", "snow", "confetti",
    "particles", "laser beam", "glowing orb", "spiral", "vortex", "hypnotic pattern",
    "abstract pattern", "geometric pattern", "glitch pattern", "pixel game scene",
    "video game character", "arcade sprite", "computer screen", "television", "camera",
    "car", "aircraft", "rocket", "sword", "gun", "book", "candle", "cross", "symbol",
    "logo", "words", "sign", "food", "drink", "toy", "doll", "cube", "sphere",
    "three-dimensional object", "decorative frame", "decorative border", "texture",
    "brush stroke", "animated scene", "live-action person", "cartoon character",
)

FOLDER_PRIORS = {
    "radial": {"abstract"},
    "flower": {"plant", "flower"},
    "garden": {"plant"},
    "stroke": {"abstract"},
    "squares": {"glitch", "box"},
    "esp ra de glitch": {"glitch", "pixel-art", "video-game"},
    "esp ra de": {"pixel-art", "video-game"},
    "esp ra de characters": {"character", "pixel-art", "video-game"},
    "particles": {"particle"},
    "3d": {"3d"},
    "pixel art+games": {"pixel-art", "video-game"},
    "anime": {"anime", "character"},
    "framing": {"framing"},
}

GENERIC_STEMS = {
    "giphy", "tenor", "tumblr", "source", "image", "img", "ezgif", "animated",
    "animation", "transparent", "resized", "copy", "gif", "sprite", "track", "cluster",
}

KEYWORD_TAGS = {
    "flower": {"plant", "flower"}, "rose": {"plant", "flower"},
    "sunflower": {"plant", "flower"}, "plant": {"plant"}, "tree": {"plant"},
    "leaf": {"plant"}, "palm": {"plant"}, "mushroom": {"plant"},
    "cat": {"animal", "cute"}, "dog": {"animal"}, "horse": {"animal"},
    "bird": {"animal"}, "fish": {"animal"}, "butterfly": {"animal"},
    "frog": {"animal"}, "bear": {"animal"}, "dragon": {"animal"},
    "anime": {"anime", "character"}, "girl": {"character"}, "boy": {"character"},
    "baby": {"character", "cute"}, "dance": {"character"}, "dancer": {"character"},
    "cowboy": {"western", "character"}, "western": {"western"},
    "angel": {"spiritual", "character"}, "cross": {"spiritual"},
    "crucifix": {"spiritual"}, "demon": {"spiritual", "character"},
    "heart": {"cute"}, "kawaii": {"cute"}, "cute": {"cute"},
    "meme": {"meme"}, "reaction": {"meme"}, "logo": {"text"},
    "word": {"text"}, "text": {"text"}, "letter": {"text"},
    "frame": {"framing"}, "border": {"framing"}, "divider": {"framing"},
    "particle": {"particle"}, "sparkle": {"particle", "lighting"},
    "bubble": {"particle"}, "snow": {"particle"}, "confetti": {"particle"},
    "fire": {"lighting"}, "light": {"lighting"}, "laser": {"lighting"},
    "glow": {"lighting"}, "lightning": {"lighting"},
    "glitch": {"glitch"}, "datamosh": {"glitch"},
    "pixel": {"pixel-art"}, "sprite": {"pixel-art", "video-game"},
    "game": {"video-game"}, "arcade": {"video-game"}, "mario": {"video-game"},
    "pokemon": {"video-game"}, "runescape": {"video-game"}, "doom": {"video-game"},
    "cube": {"3d"}, "sphere": {"3d"}, "3d": {"3d"},
    "star": {"abstract", "lighting"}, "sun": {"abstract", "lighting"},
}

CONCEPT_TAGS = {
    "flower": {"plant", "flower"}, "rose": {"plant", "flower"},
    "sunflower": {"plant", "flower"}, "bouquet": {"plant", "flower"},
    "leaf": {"plant"}, "plant": {"plant"}, "tree": {"plant"},
    "palm tree": {"plant"}, "mushroom": {"plant"}, "fruit": {"plant"},
    "butterfly": {"animal"}, "bird": {"animal"}, "cat": {"animal", "cute"},
    "dog": {"animal"}, "horse": {"animal"}, "fish": {"animal"},
    "frog": {"animal"}, "rabbit": {"animal", "cute"}, "bear": {"animal"},
    "insect": {"animal"}, "dragon": {"animal"}, "dinosaur": {"animal"},
    "animal": {"animal"}, "anime girl": {"anime", "character"},
    "anime boy": {"anime", "character"}, "woman": {"character"},
    "man": {"character"}, "child": {"character"}, "baby": {"character", "cute"},
    "dancer": {"character"}, "face": {"character"}, "hand": {"character"},
    "character": {"character"}, "angel": {"character", "spiritual"},
    "demon": {"character", "spiritual"}, "ghost": {"character", "spiritual"},
    "skull": {"spiritual"}, "wizard": {"character", "spiritual"},
    "cowboy": {"character", "western"}, "fire": {"lighting"},
    "flame": {"lighting"}, "lightning": {"lighting"}, "rainbow": {"lighting"},
    "sparkles": {"particle", "lighting"}, "explosion": {"particle", "lighting"},
    "bubbles": {"particle"}, "snow": {"particle"}, "confetti": {"particle"},
    "particles": {"particle"}, "laser beam": {"lighting"},
    "glowing orb": {"lighting"}, "spiral": {"abstract"}, "vortex": {"abstract"},
    "hypnotic pattern": {"abstract"}, "abstract pattern": {"abstract"},
    "geometric pattern": {"abstract"}, "glitch pattern": {"abstract", "glitch"},
    "pixel game scene": {"pixel-art", "video-game"},
    "video game character": {"character", "pixel-art", "video-game"},
    "arcade sprite": {"pixel-art", "video-game"}, "logo": {"text"},
    "words": {"text"}, "sign": {"text"}, "decorative frame": {"framing"},
    "decorative border": {"framing"}, "texture": {"abstract"},
    "brush stroke": {"abstract"}, "live-action person": {"character", "live-action"},
    "cartoon character": {"character", "cartoon"}, "symbol": {"abstract"},
    "cube": {"3d"}, "sphere": {"3d"}, "three-dimensional object": {"3d"},
}


Image.MAX_IMAGE_PIXELS = None
ImageFile.LOAD_TRUNCATED_IMAGES = True


def load_catalog() -> list[dict]:
    snippet = (
        "global.window=global;require('./stock-brushes.js');"
        "process.stdout.write(JSON.stringify(STOCK_BRUSH_FOLDERS));"
    )
    return json.loads(subprocess.check_output(["node", "-e", snippet], cwd=ROOT))


def clean_filename(path: str) -> str:
    stem = Path(path).stem
    stem = unicodedata.normalize("NFKC", stem)
    stem = re.sub(r"(?i)_?transparent|_?resized(?:_\d+x\d+)?|_w\d+|\s+copy(?:\s+\d+)?$", " ", stem)
    stem = re.sub(r"(?i)^ezgif[-_ ]*[a-f0-9]+$|^tumblr[_-].*$|^giphy(?:\s*\([^)]*\))?$", "", stem)
    stem = re.sub(r"(?i)^track_\d+_v\d+_m\d+_slot\d+$|^cluster_\d+_\d+x\d+$", "", stem)
    stem = re.sub(r"(?i)^\d{3}_[a-z0-9]+_\d+(?:_\d+)?$", "", stem)
    stem = re.sub(r"[_+.-]+", " ", stem)
    stem = re.sub(r"\s+", " ", stem).strip(" ()[]-_")
    tokens = re.findall(r"[a-z0-9]+", stem.lower())
    if not stem or all(t in GENERIC_STEMS or re.fullmatch(r"[a-f0-9]{5,}", t) or t.isdigit() for t in tokens):
        return ""
    if any(len(t) >= 18 and re.fullmatch(r"[a-z0-9]+", t) for t in tokens):
        return ""
    if re.fullmatch(r"[A-Z0-9]{12,}", Path(path).stem) or re.fullmatch(r"[a-f0-9]{8,}(?:\s+w\d+)?", stem, re.I):
        return ""
    if len(stem) <= 4 and not any(ch.isspace() for ch in stem):
        return ""
    return smart_title(stem)


def smart_title(value: str) -> str:
    small = {"a", "an", "and", "at", "for", "in", "of", "on", "the", "to", "with"}
    value = re.sub(r"(?i)\b3d(?=[a-z])", "3D ", value)
    value = re.sub(r"(?<=\d)(?=[A-Za-z])|(?<=[a-z])(?=[A-Z])", " ", value)
    words = re.findall(r"[A-Za-z0-9]+(?:'[A-Za-z0-9]+)?", value)
    result = []
    for i, word in enumerate(words):
        lower = word.lower()
        if lower in {"3d": "3D", "cgi": "CGI", "tv": "TV", "n64": "N64"}:
            result.append({"3d": "3D", "cgi": "CGI", "tv": "TV", "n64": "N64"}[lower])
        elif i and lower in small:
            result.append(lower)
        else:
            result.append(lower.capitalize())
    return " ".join(result)[:64]


def representative_frames(path: Path) -> tuple[list[Image.Image], dict]:
    asset_info = inspect_asset(path)
    with Image.open(path) as image:
        count = max(1, int(getattr(image, "n_frames", 1)))
        indices = sorted(set((0, count // 2, count - 1)))
        frames = []
        edge_coverages = []
        opaque_coverages = []
        palette_sizes = []
        for index in indices:
            try:
                image.seek(index)
                frame = image.convert("RGBA")
            except (EOFError, OSError):
                continue
            alpha = np.asarray(frame.getchannel("A"), dtype=np.uint8)
            edge = np.concatenate((alpha[0], alpha[-1], alpha[:, 0], alpha[:, -1]))
            edge_coverages.append(float(np.mean(edge > 24)))
            opaque_coverages.append(float(np.mean(alpha > 24)))
            sample = frame.convert("RGB").resize((64, 64), Image.Resampling.NEAREST)
            palette_sizes.append(len(sample.getcolors(maxcolors=4097) or []))
            background = Image.new("RGBA", frame.size, (255, 255, 255, 255))
            background.alpha_composite(frame)
            frames.append(background.convert("RGB"))
        if not frames:
            raise OSError("no decodable frames")
        return frames, {
            **asset_info,
            "edgeCoverage": max(edge_coverages or [0]),
            "opaqueCoverage": max(opaque_coverages or [0]),
            "paletteSize": min(palette_sizes or [4096]),
        }


def encode_text(model, processor, device, values: list[str]) -> torch.Tensor:
    tokens = processor(text=values, padding=True, return_tensors="pt")
    tokens = {key: value.to(device) for key, value in tokens.items()}
    with torch.inference_mode():
        features = model.get_text_features(**tokens)
    return features / features.norm(dim=-1, keepdim=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=str(ROOT / ".brush-analysis-results.json"))
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--batch-size", type=int, default=48)
    args = parser.parse_args()

    folders = load_catalog()
    entries = []
    seen = set()
    for folder in folders:
        folder_id = str(folder.get("id") or folder.get("name") or "misc")
        for source in folder.get("files", []):
            if source not in seen:
                entries.append({"source": source, "folder": folder_id})
                seen.add(source)
    if args.limit:
        entries = entries[: args.limit]

    device = "mps" if torch.backends.mps.is_available() else "cpu"
    processor = CLIPProcessor.from_pretrained(MODEL_NAME)
    model = CLIPModel.from_pretrained(MODEL_NAME, use_safetensors=False).to(device).eval()
    tag_features = encode_text(
        model, processor, device,
        [f"an animated GIF brush showing {TAG_PROMPTS[tag]}" for tag in ALLOWED_TAGS],
    )
    concept_features = encode_text(
        model, processor, device,
        [f"an animated GIF of {concept}" for concept in CONCEPTS],
    )

    prepared = []
    failures = []
    for index, entry in enumerate(entries, 1):
        try:
            frames, stats = representative_frames(ROOT / entry["source"])
            prepared.append((entry, frames, stats))
        except Exception as error:
            failures.append({**entry, "error": str(error)})
        if index % 250 == 0:
            print(f"decoded {index}/{len(entries)}", file=sys.stderr, flush=True)

    results = []
    frame_batch = []
    frame_owners = []

    def flush_batch() -> None:
        nonlocal frame_batch, frame_owners
        if not frame_batch:
            return
        inputs = processor(images=frame_batch, return_tensors="pt")
        inputs = {key: value.to(device) for key, value in inputs.items()}
        with torch.inference_mode():
            features = model.get_image_features(**inputs)
        features = features / features.norm(dim=-1, keepdim=True)
        tag_scores = (features @ tag_features.T).float().cpu().numpy()
        concept_scores = (features @ concept_features.T).float().cpu().numpy()
        for row, owner in enumerate(frame_owners):
            owner["tagFrames"].append(tag_scores[row])
            owner["conceptFrames"].append(concept_scores[row])
        frame_batch = []
        frame_owners = []

    holders = []
    for entry, frames, stats in prepared:
        holder = {**entry, **stats, "tagFrames": [], "conceptFrames": []}
        holders.append(holder)
        for frame in frames:
            frame_batch.append(frame)
            frame_owners.append(holder)
            if len(frame_batch) >= args.batch_size:
                flush_batch()
    flush_batch()

    for holder in holders:
        tag_scores = np.asarray(holder.pop("tagFrames")).mean(axis=0)
        concept_scores = np.asarray(holder.pop("conceptFrames")).mean(axis=0)
        tags = choose_tags(holder, tag_scores, concept_scores)
        concept_order = np.argsort(-concept_scores)[:8]
        concepts = [{"name": CONCEPTS[i], "score": round(float(concept_scores[i]), 5)} for i in concept_order]
        results.append({
            **holder,
            "filenameName": clean_filename(holder["source"]),
            "tags": tags,
            "tagScores": {tag: round(float(score), 5) for tag, score in zip(ALLOWED_TAGS, tag_scores)},
            "concepts": concepts,
        })

    output = {
        "model": MODEL_NAME,
        "allowedTags": list(ALLOWED_TAGS),
        "assets": results,
        "failures": failures,
    }
    Path(args.output).write_text(json.dumps(output, ensure_ascii=False, indent=2) + "\n")
    print(f"wrote {len(results)} assets; {len(failures)} failures to {args.output}", file=sys.stderr)


def choose_tags(holder: dict, scores: np.ndarray, concept_scores: np.ndarray) -> list[str]:
    score = {tag: float(value) for tag, value in zip(ALLOWED_TAGS, scores)}
    tags = set(FOLDER_PRIORS.get(holder["folder"], set()))
    filename_words = set(re.findall(r"[a-z0-9]+", Path(holder["source"]).stem.lower()))
    for word in filename_words:
        tags.update(KEYWORD_TAGS.get(word, set()))

    concept_order = np.argsort(-concept_scores)
    if len(concept_order):
        tags.update(CONCEPT_TAGS.get(CONCEPTS[int(concept_order[0])], set()))
    if len(concept_order) > 1 and concept_scores[concept_order[0]] - concept_scores[concept_order[1]] <= 0.006:
        secondary = CONCEPT_TAGS.get(CONCEPTS[int(concept_order[1])], set())
        if secondary & {"plant", "flower", "animal", "character", "text", "particle", "lighting", "framing"}:
            tags.update(secondary)

    semantic_groups = (
        ("anime", "pixel-art", "glitch", "3d", "video-game", "cartoon", "illustration", "live-action"),
    )
    for group_index, group in enumerate(semantic_groups):
        ranked = sorted(group, key=score.get, reverse=True)
        values = [score[tag] for tag in group]
        best = score[ranked[0]]
        required_lift = (0.012,)[group_index]
        required_margin = 0.018 if ranked[0] == "pixel-art" else (0.002,)[group_index]
        if best >= (0.24,)[group_index] and best - float(np.mean(values)) >= required_lift and best - score[ranked[1]] >= required_margin:
            tags.add(ranked[0])

    # Closely related semantic pairs are useful together when evidence supports both.
    if "flower" in tags:
        tags.add("plant")
    if "anime" in tags:
        tags.update(("character", "illustration"))

    # A rectangle whose visible pixels reach most edges matches the user's box rule.
    if holder["edgeCoverage"] >= 0.70 and holder["opaqueCoverage"] >= 0.72:
        tags.add("box")
    elif holder["edgeCoverage"] < 0.28:
        tags.discard("box")

    # Box-like game/glitch captures often resemble a border to the model, but
    # framing is reserved for assets intended to decorate the canvas edge.
    if holder["folder"] in {"squares", "esp ra de glitch"} and not ({"frame", "border"} & filename_words):
        tags.discard("framing")

    tags.discard("misc")
    # Keep the visible tag row useful instead of echoing every near-tied model
    # score. Source priors and filename evidence win ties deterministically.
    if len(tags) > 7:
        protected = set(FOLDER_PRIORS.get(holder["folder"], set()))
        protected.update(tag for word in filename_words for tag in KEYWORD_TAGS.get(word, set()))
        protected.add("box") if "box" in tags else None
        remaining = sorted(tags - protected, key=lambda tag: score[tag], reverse=True)
        tags = protected | set(remaining[: max(0, 7 - len(protected))])
    if not tags:
        tags.add("misc")
    return [tag for tag in ALLOWED_TAGS if tag in tags]


if __name__ == "__main__":
    main()
