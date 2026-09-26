# Preview rendering and export options

Native GIF/CSS animation is the default at every stamp count. The **smooth render
preview** checkbox at the bottom of **gif samples** opts into the existing export
raster worker for the preview. It presents one complete canvas frame rather than
compositing hundreds of independently animated/filter surfaces. The setting is
saved in sessions, bookmarks and backups as `smoothRenderPreview`; older records
without that field use the new native default. No flashing or crop escapes are
artificially generated. Preview settings do not affect normal export pixels.

Only one preview frame may be in flight. The previous frame remains visible until
the next one is complete. The worker uses a bounded decode budget, and each
transferred ImageBitmap is closed after display. Preview frames are capped at
1200×900 and target 20fps; slower devices present fewer complete frames rather
than partial compositions. Native rendering has no application frame cap. Actual
speed and rendering artifacts depend on the browser and GPU.

The DOM remains available for paused crop inspection. Previews resume after
inspection, visibility changes, context restoration, and back/forward navigation.
Starting a normal export or replacing a composition retires the previous preview
worker. Realtime recording leaves the selected preview renderer running. Preview
errors restore native rendering and report the error.

The download icon opens **export options**. Defaults are **Downloads**, **6 sec**,
**mp4**, **normal**. Duration ranges from 1–15 seconds for both formats and both
rendering modes. Normal exports render full-resolution clean frames. WebP retains
its existing loop planning and lossless frames; MP4 remains 30fps H.264.

Downloads follows the browser's configured download location. Where the
[File System Access API](https://developer.chrome.com/docs/capabilities/web-apis/file-system-access)
is available, **choose folder…** opens a native directory picker starting in
Downloads. The directory handle is kept only for this page session. Export files
are written directly there, with numbered names to preserve existing files.
Unsupported browsers explain how to use the browser's ask-where-to-save setting.

**Realtime** asks the browser to share this generator tab without audio and records
the actual video stream with MediaRecorder. The options modal closes before
sharing so its backdrop does not cover the artwork. **finish & save** and
**cancel recording** remain in the bottom toolbar; the options modal reopens with
the result when the recording is finished. Escape cancels. Sharing stops on
completion, cancellation, failure and navigation, including a late permission
grant after cancellation.

Where [Region Capture](https://developer.chrome.com/docs/web-platform/region-capture)
is available, the stream is cropped to the artwork. Otherwise the whole tab is
recorded, as explained in the popup. Known screen/window selections and crop
failures are rejected with guidance to choose this tab. Realtime MP4 records VP8 video where supported, then converts the captured
frames to a seekable H.264 MP4 using explicit 30fps timestamps and a complete
sample table. This avoids saving browser MP4 recorder fragments directly.
Capture requests at most 1920×1080 at 30fps to limit live encoding load. MP4
conversion requires WebCodecs; unsupported combinations are disabled.
Realtime WebP first records a video, stops sharing, then samples its actual frames
at 20fps into an animated WebP. It does not reconstruct the composition. Recording
and WebP frame storage each have a 128MiB limit; conversion is cancellable.

Realtime output uses the displayed size and achieved capture frame rate, with
additional encoder work. Display/driver artifacts may not appear in the browser's
capture stream. Neither mode guarantees a particular frame rate on all devices.

The footer's far-right status shows a circular spinner while the initial native
GIF loads settle (including failures), or until the first complete worker frame.
Once loaded, a one-second sample below 24fps shows **[low fps]**; the indicator
clears after a faster sample. Stable-mode sampling counts completed worker frames;
native-mode sampling counts animation-frame callbacks, not individual GIF frame
rates or GPU presentation. Samples reset on visibility and renderer changes and
are suppressed during loading and crop inspection. Both indicators disappear
with the information bars.

Sidebar pointer, scroll, keyboard, and input activity defers new stable-preview
requests for 180ms. The current complete frame remains visible. Worker requests
also leave at least 16ms between frames. Cached brush URLs reduce frame-planning
allocations. Native mode deliberately leaves GIF animation to the browser.

Run:

```sh
node scripts/tests/run-generator-live-capture-regression.mjs
node scripts/tests/run-generator-tab-capture-smoke.mjs
node scripts/tests/run-generator-stability-regression.mjs
node scripts/tests/run-generator-export-regression.mjs
node scripts/tests/run-generator-regression.mjs
node scripts/tests/run-generator-bookmark-regression.mjs
node scripts/tests/run-generator-performance-regression.mjs
```

The stability suite exercises 300 GIFs at a high-DPI touch viewport, checks
complete-frame submission, one-frame backpressure, unchanged sidebar screenshots,
crop inspection, pause/resume, context restoration, injected renderer failure and
recovery, native-mode bypass, unchanged stamp count/signature, loading and low-FPS
indicators, sidebar priority, clean exports in both modes, and saved checkbox
restoration. These are Chromium tests on macOS, not physical Surface or
cross-browser validation.

The live capture regression uses a fixture stream with real MediaRecorder,
playback and WebP decoding. It verifies popup defaults, 6-second completion,
early finish, full-tab fallback, permission/encoder errors, cancellation and
late permission cleanup. It also checks chosen-folder writes in an isolated
origin's filesystem, collision naming, picker cancellation, revoked permission,
mobile popup bounds, and smooth-preview continuity during capture. The tab
capture smoke test uses actual Chromium tab sharing and Region Capture in an
isolated test browser; its test-only autoaccept flag selects that test tab and
checks playable cropped MP4 output and release of all capture tracks.

The realtime smoke test seeks to six points throughout a 15-second capture and
checks a changing color fixture, finite duration, and valid decoded frames.

## Exporting all bookmarks

**export all**, left of **backup**, opens the same settings popup with an extra
order control: **saved order** (oldest first, default) or **fewest gifs first**
(stamp count ascending, with saved order breaking ties). The gallery itself keeps
its existing order. A writable folder must be selected so the browser can inspect
existing files; automatic browser Downloads cannot be enumerated by the page.

The queue uses a snapshot of the bookmarks and processes one at a time. Names
include a content/settings fingerprint, duration and mode. Nonempty files matching
that exact name are skipped; unrelated or legacy filenames are not guessed to be
matches. Changing the queue order does not change filenames. Failed exports stay
marked failed; running the queue again skips completed files and retries missing
ones. Existing files are never overwritten.

Pending cards are faded, the active card has loading/progress feedback, and saved
or already-present cards return to normal. The popup closes during the queue,
leaving the gallery scrollable. Bookmark editing and composition controls are
locked until completion/cancellation, and the original composition is restored.
Temporary queue scenes are not written to the active-session backup.

Normal jobs omit the animated DOM scene during export, release their worker and
encoder after each item, and retry once with a fresh renderer before marking that
item failed and proceeding. Timeouts measure inactivity and reset on worker
progress. Storage permission/quota errors stop the queue. These measures bound
resources and prevent one broken item from stopping every subsequent item; they
cannot guarantee completion under browser crashes or device resource exhaustion.
Realtime jobs share the selected tab once, load each scene, record sequentially,
then stop sharing when finished or cancelled. Realtime failures are not retried
automatically because a second recording would capture different live frames.

Run `node scripts/tests/run-generator-batch-export-regression.mjs` for queue,
ordering, duplicate detection, fresh-renderer retry, folder saving, cancellation,
sidebar accessibility and restoration checks. Folder writes use an isolated
origin filesystem, and realtime capture uses a fixture stream with real encoding.
