// Store encoded chunks as Blobs instead of retaining a second full MP4 buffer.
// The muxer patches headers by position; preserve those writes without changing
// the standard seekable MP4 container used by normal exports.
export function createQualityMp4Target(StreamTarget) {
  let sections = [];
  const target = new StreamTarget({
    chunked: true,
    chunkSize: 1024 * 1024,
    onData(data, position) {
      const end = position + data.byteLength;
      const next = [];
      for (const section of sections) {
        if (section.end <= position || section.start >= end) next.push(section);
        else {
          if (section.start < position) next.push({ start: section.start, end: position,
            blob: section.blob.slice(0, position - section.start) });
          if (section.end > end) next.push({ start: end, end: section.end,
            blob: section.blob.slice(end - section.start) });
        }
      }
      next.push({ start: position, end, blob: new Blob([data]) });
      sections = next.sort((a, b) => a.start - b.start);
    }
  });
  return {
    target,
    finish() {
      let end = 0;
      for (const section of sections) {
        if (section.start !== end) throw new Error("Quality MP4 contains an incomplete chunk.");
        end = section.end;
      }
      const blob = new Blob(sections.map(section => section.blob), { type: "video/mp4" });
      sections = [];
      return blob;
    }
  };
}
