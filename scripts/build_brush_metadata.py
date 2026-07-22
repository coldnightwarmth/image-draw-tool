#!/usr/bin/env python3
"""Turn audited brush-analysis output into the browser's static metadata map."""

from __future__ import annotations

import argparse
import collections
import json
import re
from pathlib import Path

from brush_asset_info import inspect_asset


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_TAGS = (
    "plant", "flower", "animal", "character", "anime", "pixel-art",
    "glitch", "3d", "video-game", "cartoon", "illustration",
    "live-action", "abstract", "text", "framing", "particle",
    "lighting", "box", "cute", "spiritual", "western", "meme", "misc",
)

FALLBACK_NAMES = {
    "radial": "Radial Effect",
    "flower": "Animated Flower",
    "garden": "Garden Element",
    "stroke": "Animated Brush Stroke",
    "squares": "Glitch Tile",
    "esp ra de glitch": "Pixel Glitch Fragment",
    "esp ra de": "Pixel Game Sprite",
    "esp ra de characters": "Pixel Game Character",
    "particles": "Particle Effect",
    "3d": "3D Object",
    "pixel art+games": "Pixel Game Sprite",
    "anime": "Anime Character",
    "misc": "Animated Element",
    "framing": "Animated Frame",
    "nu": "Animated Element",
}

GENERIC_CONCEPTS = {
    "animated scene", "symbol", "character", "animal", "plant", "particles",
    "abstract pattern", "geometric pattern", "three-dimensional object",
}

FOLDER_PROTECTED_TAGS = {
    "radial": {"abstract"}, "flower": {"plant", "flower"},
    "garden": {"plant"}, "stroke": {"abstract"},
    "squares": {"glitch"}, "esp ra de glitch": {"glitch", "pixel-art", "video-game"},
    "esp ra de": {"pixel-art", "video-game"},
    "esp ra de characters": {"character", "pixel-art", "video-game"},
    "particles": {"particle"}, "3d": {"3d"},
    "pixel art+games": {"pixel-art", "video-game"},
    "anime": {"anime", "character", "illustration"}, "framing": {"framing"},
}

CAPTION_TAG_PATTERNS = {
    "flower": r"\b(flower|flowers|rose|roses|sunflower|daisy|tulip|blossom|bouquet|petals?)\b",
    "plant": r"\b(plant|plants|flower|flowers|rose|tree|forest|leaf|leaves|vine|grass|mushroom|cactus|palm|bouquet|fruit)\b",
    "animal": r"\b(animal|bird|duck|chicken|eagle|owl|cat|kitten|dog|puppy|horse|pony|fish|whale|dolphin|frog|rabbit|bunny|bear|lion|tiger|elephant|monkey|butterfl(?:y|ies)|bee|insect|dragon|dinosaur|reptile|snake|mouse|rat|sheep|ram|deer|fox|wolf|pig|cow|goat|turtle|snail)\b",
    "character": r"\b(person|people|man|men|woman|women|boy|girl|child|baby|dancer|character|figure|doll|wizard|witch|cowboy|cowgirl|angel|demon|superhero|soldier|robot|face)\b",
    "anime": r"\b(anime|manga)\b",
    "pixel-art": r"\b(pixel(?: art|ated|ed)?|sprite)\b",
    "glitch": r"\b(glitch|glitched|distorted pixels?|digital distortion)\b",
    "3d": r"\b(3d|three dimensional|computer generated|rendered|rendering)\b",
    "video-game": r"\b(video game|arcade|game screenshot|game character|sprite)\b",
    "cartoon": r"\b(cartoon|comic)\b",
    "illustration": r"\b(drawing|illustration|illustrated|painting|watercolor|map|cartoon|anime|clip art)\b",
    "live-action": r"\b(photo|photograph|live action)\b",
    "abstract": r"\b(abstract|pattern|geometric|spiral|swirl|vortex|fractal|kaleidoscope|shape|circle|square|triangle)\b",
    "text": r"\b(text|words?|letters?|sign|caption|typography|says|written)\b",
    "framing": r"\b(frame|border|divider|corner decoration)\b",
    "particle": r"\b(particles?|sparkles?|sparks?|bubbles?|confetti|snowflakes?|floating dots?)\b",
    "lighting": r"\b(lightning|laser|glow|glowing|neon|light beam|flame|fire|flash|shining|luminous)\b",
    "cute": r"\b(cute|adorable|kawaii|heart|smiley)\b",
    "spiritual": r"\b(angel|demon|cross|crucifix|religious|spiritual|sacred|church|buddha|prayer|halo|goddess|occult)\b",
    "western": r"\b(cowboy|cowgirl|western|texas|old west|frontier)\b",
    "meme": r"\b(meme|reaction image)\b",
}


def title_case(value: str) -> str:
    small = {"a", "an", "and", "at", "for", "in", "of", "on", "the", "to", "with"}
    replacements = {"3d": "3D", "cgi": "CGI", "tv": "TV", "n64": "N64"}
    words = re.findall(r"[A-Za-z0-9]+(?:'[A-Za-z0-9]+)?", value)
    result = []
    for index, word in enumerate(words):
        lower = word.lower()
        result.append(replacements.get(lower, lower if index and lower in small else lower.capitalize()))
    return " ".join(result)


def choose_name(asset: dict) -> str:
    tags = set(asset["tags"])
    caption = clean_caption(asset.get("caption"))
    if caption:
        name = title_case(caption)
        lowered = name.lower()
        folder = asset.get("folder")
        if folder == "anime" and "anime" not in lowered:
            name = f"Anime {name}"
        elif folder in {"esp ra de", "esp ra de characters", "pixel art+games"} and not any(word in lowered for word in ("pixel", "arcade", "game", "sprite")):
            name = f"Pixel {name}"
        elif folder == "3d" and not any(word in lowered for word in ("3d", "render", "cube", "sphere")):
            name = f"3D {name}"
        if folder in {"squares", "esp ra de glitch"} and "glitch" not in name.lower():
            name = f"{name} Glitch"
        return name[:64]

    concepts = [str(item["name"]) for item in asset.get("concepts", [])]
    concept = next((item for item in concepts if item not in GENERIC_CONCEPTS), "")
    if not concept:
        return FALLBACK_NAMES.get(asset["folder"], "Animated Element")

    name = title_case(concept)
    lowered = name.lower()
    if "anime" in tags and "anime" not in lowered:
        name = f"Anime {name}"
    elif "pixel-art" in tags and not any(word in lowered for word in ("pixel", "arcade", "game")):
        name = f"Pixel {name}"
    elif "3d" in tags and not any(word in lowered for word in ("3d", "cube", "sphere")):
        name = f"3D {name}"
    if "glitch" in tags and "glitch" not in name.lower():
        name = f"{name} Glitch"
    if "framing" in tags and not any(word in name.lower() for word in ("frame", "border")):
        name = f"{name} Frame"
    return name[:64]


def clean_caption(raw_caption) -> str:
    caption = " ".join(str(raw_caption or "").strip().lower().split())
    if not caption:
        return ""
    caption = re.split(r",|\s+-\s+", caption, maxsplit=1)[0]
    background_match = re.match(r"^(?:an? |the )?(?:white|black) background with (.+)$", caption)
    if background_match:
        caption = background_match.group(1)
    caption = re.sub(
        r"^(?:there is |this is )?(?:an? )?(?:image|picture|photo|photograph|drawing|illustration|cartoon|clip art|computer generated image|close up) of ",
        "",
        caption,
    )
    caption = re.sub(
        r"^(?:an? |the )?(?:(?:black and white|colorful|pixeled|pixelated|computer generated) )?(?:image|picture|photo|photograph|drawing|illustration) of ",
        "",
        caption,
    )
    caption = re.sub(r"^(?:an?|the)\s+", "", caption)
    caption = re.split(
        r"\s+(?:on|against) (?:an? )?(?:plain )?(?:white|black|transparent) background\b|\s+with (?:an? )?(?:plain )?(?:white|black) background\b",
        caption,
        maxsplit=1,
    )[0]
    words_without_runs = []
    for word in caption.split():
        if words_without_runs and word == words_without_runs[-1]:
            continue
        words_without_runs.append(word)
    caption = " ".join(words_without_runs)
    caption = re.sub(r"\s+", " ", caption).strip(" .,-")
    caption = re.sub(r"(?:\s+\b(?:of|with|in|on|at|to|for|and|the|a|an)\b)+$", "", caption).strip()
    words = caption.split()
    if len(words) > 8:
        caption = " ".join(words[:8])
    caption = re.sub(r"(?:\s+\b(?:of|with|in|on|at|to|for|and|the|a|an)\b)+$", "", caption).strip()
    if caption in {
        "image", "picture", "animation", "animated image", "object", "colorful",
        "tall", "logo", "icon", "snowflstring",
    } or re.match(
        r"^(?:the )?logo for (?:(?:the )?new\b|the game$)", caption
    ):
        return ""
    return caption


def refine_tags(asset: dict) -> list[str]:
    tags = set(asset.get("tags") or [])
    caption = str(asset.get("caption") or "").lower()
    caption_tags = {
        tag for tag, pattern in CAPTION_TAG_PATTERNS.items() if re.search(pattern, caption)
    }
    protected = set(FOLDER_PROTECTED_TAGS.get(asset.get("folder"), set()))
    subject_tags = {"plant", "flower", "animal", "character"}
    supported_subjects = caption_tags & subject_tags
    object_only = re.search(
        r"\b(aircraft|balloon|bag|bell|bill|brain|candle|cards?|car|circle|computer|cross|crown|cube|diamond|food|frame|gun|ice cream|icon|key|logo|map|monitor|nut|orb|pattern|planet|ring|robot|sign|sphere|star|sword|television|vase)\b",
        caption,
    )
    if caption and (supported_subjects or object_only):
        # BLIP's explicit subject nouns are more reliable than a near-tied CLIP
        # concept score. Protected source semantics are never removed.
        tags.difference_update((subject_tags - supported_subjects) - protected)
    source_words = set(re.findall(r"[a-z0-9]+", str(asset.get("source") or "").lower()))
    source_evidence = {
        "text": {"text", "word", "words", "letter", "letters", "logo", "sign"},
        "framing": {"frame", "border", "divider"},
        "spiritual": {"angel", "demon", "cross", "crucifix", "buddha", "prayer", "halo", "occult"},
        "western": {"cowboy", "cowgirl", "western", "texas"},
        "meme": {"meme", "reaction"},
    }
    if caption:
        for tag, words in source_evidence.items():
            if tag not in caption_tags and tag not in protected and not (source_words & words):
                tags.discard(tag)
        if object_only and not (caption_tags & {"particle", "lighting", "framing"}):
            if re.search(r"\b(cards?|crown|ice cream|key|map|nut|ring)\b", caption):
                tags.difference_update(({"particle", "lighting", "framing"} - protected))
    tags.update(caption_tags)
    concept_names = [str(item.get("name") or "") for item in asset.get("concepts", [])[:3]]
    concept_set = set(concept_names)
    source_text = str(asset.get("source") or "").lower()
    style_tags = {"anime", "pixel-art", "glitch", "3d", "video-game", "cartoon", "illustration", "live-action"}
    caption_led_style_folders = {"radial", "flower", "garden", "stroke", "squares", "particles", "framing"}
    if caption and asset.get("folder") in caption_led_style_folders:
        tags.difference_update((style_tags - caption_tags) - protected)
    if caption and asset.get("folder") in {"misc", "nu"}:
        pixel_evidence = bool(
            "pixel-art" in caption_tags
            or re.search(r"\b(pixel|sprite)\b", source_text)
            or concept_set & {"pixel game scene", "video game character", "arcade sprite"}
        )
        if not pixel_evidence:
            tags.discard("pixel-art")
        three_d_evidence = bool(
            "3d" in caption_tags
            or re.search(r"\b3d\b", source_text)
            or concept_set & {"cube", "sphere", "three-dimensional object"}
        )
        if not three_d_evidence:
            tags.discard("3d")
        if "logo" in caption or "words" in concept_set:
            tags.add("text")
        if "live-action person" in concept_set and "character" in tags and not (
            {"anime", "pixel-art", "cartoon"} & tags
        ):
            tags.add("live-action")
    if re.search(r"\b(smiley|smiling face)\b", caption):
        tags.update(("cartoon", "cute"))
    if asset.get("folder") not in {"misc", "nu"}:
        tags.discard("live-action")
    if "flower" in tags:
        tags.add("plant")
    if "anime" in tags:
        tags.update(("character", "illustration"))
    if "live-action" in caption_tags:
        tags.discard("pixel-art")
    tags.update(protected)
    tags.intersection_update(ALLOWED_TAGS)
    if not tags:
        tags.add("misc")
    return [tag for tag in ALLOWED_TAGS if tag in tags]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=str(ROOT / ".brush-analysis-results.json"))
    parser.add_argument("--output", default=str(ROOT / "brush-metadata.js"))
    args = parser.parse_args()

    payload = json.loads(Path(args.input).read_text())
    allowed = set(ALLOWED_TAGS)
    assets = payload["assets"]
    for asset in assets:
        asset["tags"] = refine_tags(asset)
    base_names = [choose_name(asset) for asset in assets]
    totals = collections.Counter(name.casefold() for name in base_names)
    occurrences: collections.Counter[str] = collections.Counter()
    used_names = set()
    metadata = {}
    for asset, base_name in zip(assets, base_names):
        key = base_name.casefold()
        occurrences[key] += 1
        name = base_name
        if totals[key] > 1:
            name = f"{base_name} {occurrences[key]:02d}"
        unique_name = name
        suffix = 2
        while unique_name.casefold() in used_names:
            unique_name = f"{name} ({suffix})"
            suffix += 1
        name = unique_name
        used_names.add(name.casefold())
        tags = [tag for tag in asset["tags"] if tag in allowed]
        if not tags:
            tags = ["misc"]
        metadata[asset["source"]] = {
            "name": name,
            "tags": tags,
            **inspect_asset(ROOT / asset["source"]),
        }
        if len(metadata) % 250 == 0:
            print(f"inspected {len(metadata)}/{len(assets)} assets", flush=True)

    banner = (
        "// Generated by scripts/build_brush_metadata.py. Asset filenames and URLs "
        "remain unchanged.\n"
    )
    body = "window.STOCK_BRUSH_METADATA = " + json.dumps(
        metadata, ensure_ascii=False, separators=(",", ":")
    ) + ";\n"
    Path(args.output).write_text(banner + body)

    tag_counts = collections.Counter(tag for item in metadata.values() for tag in item["tags"])
    print(f"wrote {len(metadata)} metadata entries to {args.output}")
    print("tags " + ", ".join(f"{tag}={tag_counts[tag]}" for tag in ALLOWED_TAGS))


if __name__ == "__main__":
    main()
