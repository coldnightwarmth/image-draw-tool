# GIF inspection worker protocol

Create the worker as a module and send protocol version 1 messages:

```js
const worker = new Worker("./gif-inspect-worker.js", { type: "module" });

worker.postMessage({
  protocol: "gif-inspect",
  version: 1,
  type: "inspect",
  jobId: "unique-id",
  source: { url: "brush.gif" }, // alternatively: { buffer: ArrayBuffer }
  options: {
    checkOpacity: false,
    maxInputBytes: 128 * 1024 * 1024,
    maxOpacityPixels: 16 * 1024 * 1024,
  },
});
```

An inspection finishes with `result`, `error`, or `cancelled`. Every response
repeats `protocol`, `version`, and `jobId`. Errors have stable `code`,
`category`, `message`, and `retriable` fields, plus optional `details`.

Error categories are:

- `safety`: a configured hard resource limit was reached. Callers must not
  retry through a less-bounded decoder.
- `capability`: the requested protocol/runtime capability is unavailable. A
  caller may use an independently bounded fallback.
- `cancelled`: represented by the terminal `cancelled` response, not `error`.
- `input`, `network`, `protocol`, or `internal`: invalid data, fetch failures,
  caller protocol errors, or unexpected worker failures respectively.

Cancel an active job with:

```js
worker.postMessage({
  protocol: "gif-inspect",
  version: 1,
  type: "cancel",
  jobId: "unique-id",
});
```

The app only falls back for capability failures. That fallback reads at most
16 MiB through a bounded stream and parses frame metadata without decompressing
or retaining rendered GIF frames.
