#!/usr/bin/env node

import assert from "node:assert/strict";
import { createReadStream, existsSync, readFileSync, statSync } from "node:fs";
import { createServer } from "node:http";
import { dirname, extname, isAbsolute, relative, resolve, sep } from "node:path";
import { fileURLToPath } from "node:url";

const SCRIPT_DIRECTORY = dirname(fileURLToPath(import.meta.url));
const PROJECT_ROOT = resolve(SCRIPT_DIRECTORY, "../..");
const MIME_TYPES = new Map([
  [".css", "text/css; charset=utf-8"],
  [".gif", "image/gif"],
  [".html", "text/html; charset=utf-8"],
  [".js", "text/javascript; charset=utf-8"],
  [".mjs", "text/javascript; charset=utf-8"],
  [".mp4", "video/mp4"],
  [".webp", "image/webp"]
]);

function readFourCc(bytes, offset) {
  return bytes.subarray(offset, offset + 4).toString("ascii");
}

function readUint24LittleEndian(bytes, offset) {
  return bytes[offset] | (bytes[offset + 1] << 8) | (bytes[offset + 2] << 16);
}

function parseAnimatedWebp(bytes) {
  assert.equal(readFourCc(bytes, 0), "RIFF");
  assert.equal(readFourCc(bytes, 8), "WEBP");
  assert.equal(bytes.readUInt32LE(4), bytes.byteLength - 8);
  const frames = [];
  let width = 0;
  let height = 0;
  let animated = false;
  let offset = 12;
  while (offset + 8 <= bytes.byteLength) {
    const type = readFourCc(bytes, offset);
    const size = bytes.readUInt32LE(offset + 4);
    const payloadOffset = offset + 8;
    const payloadEnd = payloadOffset + size;
    assert.ok(payloadEnd <= bytes.byteLength, `${type} chunk exceeded the WebP file`);
    if (type === "VP8X") {
      animated = Boolean(bytes[payloadOffset] & 0x02);
      width = readUint24LittleEndian(bytes, payloadOffset + 4) + 1;
      height = readUint24LittleEndian(bytes, payloadOffset + 7) + 1;
    } else if (type === "ANMF") {
      const frame = {
        width: readUint24LittleEndian(bytes, payloadOffset + 6) + 1,
        height: readUint24LittleEndian(bytes, payloadOffset + 9) + 1,
        delay: readUint24LittleEndian(bytes, payloadOffset + 12),
        codec: ""
      };
      let frameOffset = payloadOffset + 16;
      while (frameOffset + 8 <= payloadEnd) {
        const frameType = readFourCc(bytes, frameOffset);
        const frameSize = bytes.readUInt32LE(frameOffset + 4);
        if (frameType === "VP8L" || frameType === "VP8 ") {
          frame.codec = frameType.trim();
        }
        frameOffset += 8 + frameSize + (frameSize % 2);
      }
      frames.push(frame);
    }
    offset = payloadEnd + (size % 2);
  }
  return { width, height, animated, frames };
}

function parseMp4(bytes) {
  const boxes = [];
  let offset = 0;
  while (offset + 8 <= bytes.byteLength) {
    let size = bytes.readUInt32BE(offset);
    const type = readFourCc(bytes, offset + 4);
    let headerSize = 8;
    if (size === 1) {
      assert.ok(offset + 16 <= bytes.byteLength, `${type} has a truncated extended size`);
      size = Number(bytes.readBigUInt64BE(offset + 8));
      headerSize = 16;
    } else if (size === 0) {
      size = bytes.byteLength - offset;
    }
    assert.ok(size >= headerSize, `${type} has an invalid MP4 box size`);
    assert.ok(offset + size <= bytes.byteLength, `${type} exceeded the MP4 file`);
    boxes.push({ type, offset, size, headerSize });
    offset += size;
  }
  assert.equal(offset, bytes.byteLength, "expected complete top-level MP4 boxes");
  const ftyp = boxes.find((box) => box.type === "ftyp");
  const moov = boxes.find((box) => box.type === "moov");
  const mdat = boxes.find((box) => box.type === "mdat");
  assert.ok(ftyp, "expected an MP4 file type box");
  assert.ok(moov, "expected an MP4 movie box");
  assert.ok(mdat, "expected an MP4 media data box");
  return {
    boxes: boxes.map((box) => box.type),
    majorBrand: readFourCc(bytes, ftyp.offset + ftyp.headerSize),
    hasAvcSampleEntry: bytes.includes(Buffer.from("avc1", "ascii")),
    hasAvcConfiguration: bytes.includes(Buffer.from("avcC", "ascii"))
  };
}

async function inspectMp4Video(page, bytes) {
  const encoded = bytes.toString("base64");
  return page.evaluate(async (encodedVideo) => {
    const binary = atob(encodedVideo);
    const data = new Uint8Array(binary.length);
    for (let index = 0; index < binary.length; index += 1) {
      data[index] = binary.charCodeAt(index);
    }
    const url = URL.createObjectURL(new Blob([data], { type: "video/mp4" }));
    const video = document.createElement("video");
    video.preload = "metadata";
    try {
      await new Promise((resolve, reject) => {
        const timeout = window.setTimeout(
          () => reject(new Error("MP4 metadata timed out")),
          15000
        );
        video.addEventListener("loadedmetadata", () => {
          window.clearTimeout(timeout);
          resolve();
        }, { once: true });
        video.addEventListener("error", () => {
          window.clearTimeout(timeout);
          reject(new Error(video.error?.message || "MP4 playback metadata failed"));
        }, { once: true });
        video.src = url;
      });
      return {
        duration: video.duration,
        width: video.videoWidth,
        height: video.videoHeight
      };
    } finally {
      video.removeAttribute("src");
      video.load();
      URL.revokeObjectURL(url);
    }
  }, encoded);
}

async function inspectFirstWebpFrame(page, bytes, margin = 0, background = [0, 0, 0]) {
  const encoded = bytes.toString("base64");
  return page.evaluate(async ({ encodedFrame, inset, expectedBackground }) => {
    const binary = atob(encodedFrame);
    const data = new Uint8Array(binary.length);
    for (let index = 0; index < binary.length; index += 1) {
      data[index] = binary.charCodeAt(index);
    }
    const bitmap = await createImageBitmap(new Blob([data], { type: "image/webp" }));
    const canvas = new OffscreenCanvas(bitmap.width, bitmap.height);
    const context = canvas.getContext("2d", { willReadFrequently: true });
    context.drawImage(bitmap, 0, 0);
    bitmap.close();
    const pixels = context.getImageData(0, 0, canvas.width, canvas.height).data;
    const corner = Array.from(pixels.subarray(0, 3));
    let visibleOutsideMargin = 0;
    for (let y = 0; y < canvas.height; y += 1) {
      for (let x = 0; x < canvas.width; x += 1) {
        if (
          x >= inset && x < canvas.width - inset &&
          y >= inset && y < canvas.height - inset
        ) {
          continue;
        }
        const pixelOffset = (y * canvas.width + x) * 4;
        if (expectedBackground.some((channel, index) =>
          Math.abs(pixels[pixelOffset + index] - channel) > 8
        )) {
          visibleOutsideMargin += 1;
        }
      }
    }
    return { width: canvas.width, height: canvas.height, corner, visibleOutsideMargin };
  }, { encodedFrame: encoded, inset: margin, expectedBackground: background });
}

function createStaticServer(rootDirectory) {
  const server = createServer((request, response) => {
    let pathname;
    try {
      pathname = decodeURIComponent(new URL(request.url || "/", "http://127.0.0.1").pathname);
    } catch {
      response.writeHead(400).end("Bad request");
      return;
    }
    const requestPath = pathname.endsWith("/") ? `${pathname}index.html` : pathname;
    let filePath = resolve(rootDirectory, `.${requestPath}`);
    const projectRelativePath = relative(rootDirectory, filePath);
    if (
      projectRelativePath === ".." ||
      projectRelativePath.startsWith(`..${sep}`) ||
      isAbsolute(projectRelativePath)
    ) {
      response.writeHead(403).end("Forbidden");
      return;
    }
    if (existsSync(filePath) && statSync(filePath).isDirectory()) {
      filePath = resolve(filePath, "index.html");
    }
    if (!existsSync(filePath) || !statSync(filePath).isFile()) {
      response.writeHead(404).end("Not found");
      return;
    }
    response.writeHead(200, {
      "Cache-Control": "no-store",
      "Content-Type": MIME_TYPES.get(extname(filePath).toLowerCase()) || "application/octet-stream"
    });
    if (request.method === "HEAD") {
      response.end();
      return;
    }
    createReadStream(filePath).pipe(response);
  });
  return new Promise((resolveServer, reject) => {
    server.once("error", reject);
    server.listen(0, "127.0.0.1", () => {
      const address = server.address();
      resolveServer({ server, url: `http://127.0.0.1:${address.port}/` });
    });
  });
}

async function waitForGeneration(page, count) {
  await page.waitForFunction(
    (expected) =>
      document.getElementById("generatorCanvas")?.getAttribute("aria-busy") === "false" &&
      document.querySelectorAll(".generator-stamp").length === expected,
    count,
    { timeout: 30000 }
  );
}

const { chromium } = await import("playwright");
const localServer = await createStaticServer(PROJECT_ROOT);
const browser = await chromium.launch({ headless: true });
const context = await browser.newContext({ viewport: { width: 1100, height: 760 } });
const page = await context.newPage();
page.setDefaultTimeout(240000);
const errors = [];
page.on("pageerror", (error) => errors.push(`page: ${error.message}`));
page.on("console", (message) => {
  if (message.type() === "error") {
    errors.push(`console: ${message.text()}`);
  }
});

try {
  await page.goto(`${localServer.url}generator/?seed=1234abcd`, { waitUntil: "domcontentloaded" });
  await waitForGeneration(page, 120);
  const downloadControl = await page.locator(".generator-download-split").evaluate((group) => {
    const buttons = Array.from(group.querySelectorAll("button"));
    return {
      labels: buttons.map((button) => button.textContent.trim()),
      widths: buttons.map((button) => button.getBoundingClientRect().width)
    };
  });
  assert.deepEqual(downloadControl.labels, ["webp", "mp4"]);
  assert.ok(
    Math.abs(downloadControl.widths[0] - downloadControl.widths[1]) < 0.1,
    "expected the WebP and MP4 halves to have equal widths"
  );
  await page.locator('[data-canvas-size="900x900"]').click();
  await page.locator("#generatorCanvasWidthInput, #generatorCanvasHeightInput").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.value = "320";
      input.dispatchEvent(new Event("change", { bubbles: true }));
    }
  });
  await page.locator("#generatorTagTab").click();
  await page.locator('.generator-source-checkbox[data-source-kind="tag"]').evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = input.value === "meme";
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.locator("#generatorCountSlider").evaluate((input) => {
    input.value = "2";
    input.dispatchEvent(new Event("input", { bubbles: true }));
  });
  await page.locator("#generatorBackgroundRandomToggle").uncheck({ force: true });
  await page.locator("#generatorBackgroundColorInput").evaluate((input) => {
    input.value = "#123456";
    input.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.locator("#generatorMarginSlider").evaluate((input) => {
    input.value = "144";
    input.dispatchEvent(new Event("input", { bubbles: true }));
  });
  await page.locator('input[name="generatorMarginMode"][value="crop"]').check({ force: true });
  await page.locator(".generator-sequence-effect-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = input.value === "image-cycle";
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.locator(".generator-sequence-timing-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = input.value === "all";
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  assert.equal(await page.evaluate(() => window.GeneratorApp.generate(0x1234abcd)), true);
  await waitForGeneration(page, 2);

  const downloadPromise = page.waitForEvent("download", { timeout: 240000 });
  await page.locator("#generatorDownloadWebpButton").click();
  const download = await downloadPromise;
  await page.waitForFunction(() => !window.GeneratorApp.getSummary().exporting);
  const downloadedPath = await download.path();
  assert.ok(downloadedPath, "expected a downloaded WebP path");
  const downloadedBytes = readFileSync(downloadedPath);
  const parsedWebp = parseAnimatedWebp(downloadedBytes);
  const result = await page.evaluate(() => {
    const summary = window.GeneratorApp.getSummary();
    return {
      ...summary.lastExport,
      exporting: summary.exporting,
      progressHidden: document.getElementById("generatorExportProgress")?.hidden,
      status: document.getElementById("generatorActionStatus")?.textContent || ""
    };
  });
  result.header = `${readFourCc(downloadedBytes, 0)}/${readFourCc(downloadedBytes, 8)}`;
  result.downloadedSize = downloadedBytes.byteLength;
  const expectedCorner = [0x12, 0x34, 0x56];
  const firstFrame = await inspectFirstWebpFrame(page, downloadedBytes, 144, expectedCorner);

  assert.ok(result, "expected an exported animated WebP result");
  assert.equal(result.format, "animated-webp");
  assert.match(result.filename, /\.webp$/);
  assert.equal(result.header, "RIFF/WEBP");
  assert.ok(result.size > 100, "expected a nonempty WebP");
  assert.equal(result.downloadedSize, result.size);
  assert.equal(result.width, 320);
  assert.equal(result.height, 320);
  assert.equal(parsedWebp.width, 320);
  assert.equal(parsedWebp.height, 320);
  assert.equal(parsedWebp.animated, true);
  assert.ok(result.durationMs >= 2500 && result.durationMs <= 6000);
  assert.ok(result.frameCount >= 2);
  assert.equal(parsedWebp.frames.length, result.frameCount);
  assert.equal(parsedWebp.frames.reduce((sum, frame) => sum + frame.delay, 0), result.durationMs);
  assert.ok(parsedWebp.frames.every((frame) => frame.codec === "VP8L"));
  assert.equal(result.lossless, true);
  assert.ok(
    firstFrame.corner.every((channel, index) => Math.abs(channel - expectedCorner[index]) <= 1),
    `expected cropped corner at #123456, received rgb(${firstFrame.corner.join(",")})`
  );
  assert.equal(result.exporting, false);
  assert.equal(result.progressHidden, true);
  assert.match(result.status, /webp ready/i);
  assert.match(result.status, /full resolution/i);

  const mp4DownloadPromise = page.waitForEvent("download", { timeout: 240000 });
  await page.locator("#generatorDownloadMp4Button").click();
  const mp4Download = await mp4DownloadPromise;
  await page.waitForFunction(() => !window.GeneratorApp.getSummary().exporting);
  const mp4Path = await mp4Download.path();
  assert.ok(mp4Path, "expected a downloaded MP4 path");
  const mp4Bytes = readFileSync(mp4Path);
  const parsedMp4 = parseMp4(mp4Bytes);
  const inspectedMp4 = await inspectMp4Video(page, mp4Bytes);
  const mp4Result = await page.evaluate(() => {
    const summary = window.GeneratorApp.getSummary();
    return {
      ...summary.lastExport,
      exporting: summary.exporting,
      progressHidden: document.getElementById("generatorExportProgress")?.hidden,
      status: document.getElementById("generatorActionStatus")?.textContent || ""
    };
  });

  assert.equal(mp4Result.format, "mp4");
  assert.match(mp4Result.filename, /\.mp4$/);
  assert.ok(mp4Result.size > 1000, "expected a nonempty MP4");
  assert.equal(mp4Bytes.byteLength, mp4Result.size);
  assert.equal(mp4Result.width, 320);
  assert.equal(mp4Result.height, 320);
  assert.equal(mp4Result.encodedWidth, 320);
  assert.equal(mp4Result.encodedHeight, 320);
  assert.equal(mp4Result.durationMs, 6000);
  assert.equal(mp4Result.frameCount, 180);
  assert.equal(mp4Result.fps, 30);
  assert.match(mp4Result.codec, /^avc1\./);
  assert.ok(mp4Result.bitrate >= 1_500_000);
  assert.match(parsedMp4.majorBrand, /^(isom|iso\d|mp4\d)$/);
  assert.equal(parsedMp4.hasAvcSampleEntry, true);
  assert.equal(parsedMp4.hasAvcConfiguration, true);
  assert.ok(Math.abs(inspectedMp4.duration - 6) < 0.02);
  assert.equal(inspectedMp4.width, 320);
  assert.equal(inspectedMp4.height, 320);
  assert.equal(mp4Result.exporting, false);
  assert.equal(mp4Result.progressHidden, true);
  assert.match(mp4Result.status, /mp4 ready/i);
  assert.match(mp4Result.status, /6\.0s/i);
  assert.match(mp4Result.status, /full resolution/i);

  await page.locator(".generator-sequence-effect-checkbox").evaluateAll((inputs) => {
    for (const input of inputs) {
      input.checked = input.value === "blur";
    }
    inputs[0]?.dispatchEvent(new Event("change", { bubbles: true }));
  });
  await page.waitForFunction(() => {
    const summary = window.GeneratorApp.getSummary();
    return document.getElementById("generatorCanvas")?.getAttribute("aria-busy") === "false" &&
      Number(summary.sequenceEffectCounts.blur || 0) > 0;
  });

  await page.locator("#generatorCropInspectButton").click();
  await page.locator(".generator-stamp").first().evaluate((stamp) => stamp.click());
  await page.locator("#generatorCropInspectButton").click();
  assert.equal((await page.evaluate(() => window.GeneratorApp.getSummary())).uncroppedCount, 1);

  const uncroppedDownloadPromise = page.waitForEvent("download", { timeout: 240000 });
  await page.locator("#generatorDownloadWebpButton").click();
  const uncroppedDownload = await uncroppedDownloadPromise;
  await page.waitForFunction(() => !window.GeneratorApp.getSummary().exporting);
  const uncroppedPath = await uncroppedDownload.path();
  assert.ok(uncroppedPath, "expected an uncropped-layer WebP path");
  const uncroppedBytes = readFileSync(uncroppedPath);
  const parsedBlurWebp = parseAnimatedWebp(uncroppedBytes);
  assert.ok(parsedBlurWebp.frames.length > 1, "expected multiple blur animation frames");
  assert.ok(
    parsedBlurWebp.frames.every((frame) => frame.codec === "VP8L"),
    "expected every blur frame to use lossless full-color WebP"
  );
  const uncroppedFrame = await inspectFirstWebpFrame(page, uncroppedBytes, 144, expectedCorner);
  assert.ok(
    uncroppedFrame.visibleOutsideMargin > 0,
    "expected the selected GIF to render above the crop margin"
  );

  const cancelled = await page.evaluate(async () => {
    const exportPromise = window.GeneratorApp.exportWebp({ download: false });
    window.setTimeout(() => window.GeneratorApp.cancelExport(), 25);
    const value = await exportPromise;
    return {
      value,
      exporting: window.GeneratorApp.getSummary().exporting,
      status: document.getElementById("generatorActionStatus")?.textContent || ""
    };
  });
  assert.equal(cancelled.value, null);
  assert.equal(cancelled.exporting, false);
  assert.match(cancelled.status, /cancelled/i);
  assert.deepEqual(errors, []);
  process.stdout.write(
    `generator WebP + MP4 export regression passed (${result.width}x${result.height}, ` +
    `${result.frameCount} WebP frames / ${mp4Result.frameCount} MP4 frames, ` +
    `${(result.size / 1_000_000).toFixed(2)}mb WebP / ` +
    `${(mp4Result.size / 1_000_000).toFixed(2)}mb MP4)\n`
  );
} finally {
  await context.close();
  await browser.close();
  await new Promise((resolveClose) => localServer.server.close(resolveClose));
}
