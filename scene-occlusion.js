(function attachSceneOcclusion(root, factory) {
  "use strict";

  const api = factory();

  if (typeof module === "object" && module && module.exports) {
    module.exports = api;
  }

  if (root && typeof root === "object") {
    root.SceneOcclusion = api;
  }
})(typeof globalThis !== "undefined" ? globalThis : this, function createSceneOcclusionApi() {
  "use strict";

  const DEFAULT_TILE_SIZE = 16;
  const DEFAULT_MAX_CELLS = 262144;
  const DEFAULT_MAX_EXACT_BUCKET_CELLS = 4096;

  function isFiniteNumber(value) {
    return typeof value === "number" && Number.isFinite(value);
  }

  function normalizeRect(value) {
    if (!value || typeof value !== "object") return null;

    let left;
    let top;
    let right;
    let bottom;

    if (
      isFiniteNumber(value.left) &&
      isFiniteNumber(value.top) &&
      isFiniteNumber(value.right) &&
      isFiniteNumber(value.bottom)
    ) {
      left = Math.min(value.left, value.right);
      top = Math.min(value.top, value.bottom);
      right = Math.max(value.left, value.right);
      bottom = Math.max(value.top, value.bottom);
    } else if (
      isFiniteNumber(value.x) &&
      isFiniteNumber(value.y) &&
      isFiniteNumber(value.width) &&
      isFiniteNumber(value.height)
    ) {
      left = Math.min(value.x, value.x + value.width);
      top = Math.min(value.y, value.y + value.height);
      right = Math.max(value.x, value.x + value.width);
      bottom = Math.max(value.y, value.y + value.height);
    } else {
      return null;
    }

    if (!(right > left) || !(bottom > top)) return null;

    return {
      left,
      top,
      right,
      bottom,
      width: right - left,
      height: bottom - top,
    };
  }

  function defaultRectOf(record) {
    return normalizeRect(record && record.rect ? record.rect : record);
  }

  function defaultIdOf(record, index) {
    return record && Object.prototype.hasOwnProperty.call(record, "id")
      ? record.id
      : index;
  }

  function isRecordVisible(record) {
    return Boolean(record) && record.visible !== false && record.hidden !== true;
  }

  function hasNoEffects(record) {
    if (!record || typeof record !== "object") return false;
    if (record.noEffects === true) return true;
    if (record.hasEffects === false) return true;

    const filterIsEmpty =
      record.filter === "none" || record.filter === "" || record.filter === null;
    const effectsAreEmpty =
      record.effects === false ||
      record.effects === null ||
      (Array.isArray(record.effects) && record.effects.length === 0);
    return filterIsEmpty && effectsAreEmpty;
  }

  /**
   * The default predicate is deliberately opt-in. `occluderEligible: true` is a
   * caller assertion that all of the requirements below have already been
   * checked. Otherwise every safety-relevant field must be explicit.
   */
  function isEligibleOccluder(record) {
    if (!isRecordVisible(record)) return false;
    if (record.occluderEligible === true) return true;

    const normalBlend =
      record.blendMode === "normal" || record.blendMode === "source-over";

    return (
      record.opaque === true &&
      record.opacity === 1 &&
      normalBlend &&
      hasNoEffects(record) &&
      record.axisAligned === true
    );
  }

  function rectContains(outer, inner) {
    return (
      outer.left <= inner.left &&
      outer.top <= inner.top &&
      outer.right >= inner.right &&
      outer.bottom >= inner.bottom
    );
  }

  function rectsOverlap(a, b) {
    return (
      a.left < b.right &&
      a.right > b.left &&
      a.top < b.bottom &&
      a.bottom > b.top
    );
  }

  function clampInteger(value, minimum, maximum) {
    return Math.max(minimum, Math.min(maximum, Math.trunc(value)));
  }

  function computeGrid(viewport, requestedTileSize, requestedMaxCells) {
    const baseTileSize =
      isFiniteNumber(requestedTileSize) && requestedTileSize > 0
        ? requestedTileSize
        : DEFAULT_TILE_SIZE;
    const maxCells =
      Number.isInteger(requestedMaxCells) && requestedMaxCells > 0
        ? requestedMaxCells
        : DEFAULT_MAX_CELLS;

    const minimumTileSize = Math.sqrt((viewport.width * viewport.height) / maxCells);
    const tileSize = Math.max(baseTileSize, minimumTileSize);
    const columns = Math.max(1, Math.ceil(viewport.width / tileSize));
    const rows = Math.max(1, Math.ceil(viewport.height / tileSize));

    return {
      viewport,
      tileSize,
      columns,
      rows,
      cellCount: columns * rows,
    };
  }

  function getOverlappingCellRange(rect, grid) {
    const clippedLeft = Math.max(rect.left, grid.viewport.left);
    const clippedTop = Math.max(rect.top, grid.viewport.top);
    const clippedRight = Math.min(rect.right, grid.viewport.right);
    const clippedBottom = Math.min(rect.bottom, grid.viewport.bottom);

    if (!(clippedRight > clippedLeft) || !(clippedBottom > clippedTop)) return null;

    const firstColumn = clampInteger(
      Math.floor((clippedLeft - grid.viewport.left) / grid.tileSize),
      0,
      grid.columns - 1
    );
    const lastColumn = clampInteger(
      Math.ceil((clippedRight - grid.viewport.left) / grid.tileSize) - 1,
      0,
      grid.columns - 1
    );
    const firstRow = clampInteger(
      Math.floor((clippedTop - grid.viewport.top) / grid.tileSize),
      0,
      grid.rows - 1
    );
    const lastRow = clampInteger(
      Math.ceil((clippedBottom - grid.viewport.top) / grid.tileSize) - 1,
      0,
      grid.rows - 1
    );

    return { firstColumn, lastColumn, firstRow, lastRow };
  }

  function getCellRect(column, row, grid) {
    const left = grid.viewport.left + column * grid.tileSize;
    const top = grid.viewport.top + row * grid.tileSize;
    return {
      left,
      top,
      right: Math.min(grid.viewport.right, left + grid.tileSize),
      bottom: Math.min(grid.viewport.bottom, top + grid.tileSize),
    };
  }

  function getCellIndex(column, row, grid) {
    return row * grid.columns + column;
  }

  function markFullyCoveredCells(rect, coverage, grid) {
    const range = getOverlappingCellRange(rect, grid);
    if (!range) return 0;

    let newlyCovered = 0;
    for (let row = range.firstRow; row <= range.lastRow; row += 1) {
      for (let column = range.firstColumn; column <= range.lastColumn; column += 1) {
        const cell = getCellRect(column, row, grid);
        if (!rectContains(rect, cell)) continue;

        const index = getCellIndex(column, row, grid);
        if (coverage[index] === 0) {
          coverage[index] = 1;
          newlyCovered += 1;
        }
      }
    }
    return newlyCovered;
  }

  function isCoveredByFullCells(rect, coverage, grid) {
    if (!rectContains(grid.viewport, rect)) return false;

    const range = getOverlappingCellRange(rect, grid);
    if (!range) return false;

    let checkedCell = false;
    for (let row = range.firstRow; row <= range.lastRow; row += 1) {
      for (let column = range.firstColumn; column <= range.lastColumn; column += 1) {
        const cell = getCellRect(column, row, grid);
        if (!rectsOverlap(rect, cell)) continue;
        checkedCell = true;
        if (coverage[getCellIndex(column, row, grid)] === 0) return false;
      }
    }
    return checkedCell;
  }

  function getCenterCellIndex(rect, grid) {
    const x = (rect.left + rect.right) / 2;
    const y = (rect.top + rect.bottom) / 2;
    if (
      x < grid.viewport.left ||
      x >= grid.viewport.right ||
      y < grid.viewport.top ||
      y >= grid.viewport.bottom
    ) {
      return -1;
    }

    const column = clampInteger(
      Math.floor((x - grid.viewport.left) / grid.tileSize),
      0,
      grid.columns - 1
    );
    const row = clampInteger(
      Math.floor((y - grid.viewport.top) / grid.tileSize),
      0,
      grid.rows - 1
    );
    return getCellIndex(column, row, grid);
  }

  function addExactOccluder(
    entry,
    buckets,
    largeOccluders,
    grid,
    maxExactBucketCells
  ) {
    const range = getOverlappingCellRange(entry.rect, grid);
    if (!range) return;

    const columnCount = range.lastColumn - range.firstColumn + 1;
    const rowCount = range.lastRow - range.firstRow + 1;
    if (columnCount * rowCount > maxExactBucketCells) {
      largeOccluders.push(entry);
      return;
    }

    for (let row = range.firstRow; row <= range.lastRow; row += 1) {
      for (let column = range.firstColumn; column <= range.lastColumn; column += 1) {
        const index = getCellIndex(column, row, grid);
        let bucket = buckets[index];
        if (!bucket) {
          bucket = [];
          buckets[index] = bucket;
        }
        bucket.push(entry);
      }
    }
  }

  function findContainingOccluder(rect, buckets, largeOccluders, grid) {
    for (let index = largeOccluders.length - 1; index >= 0; index -= 1) {
      if (rectContains(largeOccluders[index].rect, rect)) {
        return largeOccluders[index];
      }
    }

    const cellIndex = getCenterCellIndex(rect, grid);
    if (cellIndex < 0) return null;
    const bucket = buckets[cellIndex];
    if (!bucket) return null;

    for (let index = bucket.length - 1; index >= 0; index -= 1) {
      if (rectContains(bucket[index].rect, rect)) return bucket[index];
    }
    return null;
  }

  function emptyResult(tileSize, columns, rows, inputCount) {
    return {
      occludedIds: new Set(),
      occludedRecords: [],
      occludedEntries: [],
      stats: {
        inputCount,
        validCount: 0,
        visibleCount: 0,
        eligibleOccluderCount: 0,
        occludedCount: 0,
        exactContainmentCount: 0,
        tileCoverageCount: 0,
        fullyCoveredCellCount: 0,
        tileSize,
        columns,
        rows,
      },
    };
  }

  /**
   * Finds stamps that are definitely hidden by opaque rectangular stamps above
   * them. Records are bottom-to-top by default. Set `order: "top-to-bottom"`
   * when the input is already reversed.
   *
   * A record is only returned when `cullable === true` (or a custom
   * `isCullable` predicate returns true). This opt-in ensures the rectangle is
   * the record's complete painted footprint, including any effects.
   */
  function compute(stamps, options) {
    const records = Array.isArray(stamps) ? stamps : [];
    const config = options && typeof options === "object" ? options : {};
    const viewport = normalizeRect(config.viewport);
    if (!viewport) {
      return emptyResult(0, 0, 0, records.length);
    }

    const order = config.order || "bottom-to-top";
    if (order !== "bottom-to-top" && order !== "top-to-bottom") {
      throw new TypeError('SceneOcclusion.compute: order must be "bottom-to-top" or "top-to-bottom".');
    }

    const grid = computeGrid(viewport, config.tileSize, config.maxCells);
    const coverage = new Uint8Array(grid.cellCount);
    const exactBuckets = new Array(grid.cellCount);
    const largeOccluders = [];
    const maxExactBucketCells =
      Number.isInteger(config.maxExactBucketCells) && config.maxExactBucketCells > 0
        ? config.maxExactBucketCells
        : DEFAULT_MAX_EXACT_BUCKET_CELLS;
    const rectOf = typeof config.rectOf === "function" ? config.rectOf : defaultRectOf;
    const idOf = typeof config.idOf === "function" ? config.idOf : defaultIdOf;
    const isOccluder =
      typeof config.isOccluder === "function" ? config.isOccluder : isEligibleOccluder;
    const isCullable =
      typeof config.isCullable === "function"
        ? config.isCullable
        : (record) => Boolean(record && record.cullable === true);

    const result = emptyResult(grid.tileSize, grid.columns, grid.rows, records.length);
    const stats = result.stats;
    let fullyCoveredCellCount = 0;

    const firstIndex = order === "bottom-to-top" ? records.length - 1 : 0;
    const endIndex = order === "bottom-to-top" ? -1 : records.length;
    const step = order === "bottom-to-top" ? -1 : 1;

    for (let index = firstIndex; index !== endIndex; index += step) {
      const record = records[index];
      let rect = null;
      try {
        rect = normalizeRect(rectOf(record, index));
      } catch (_error) {
        rect = null;
      }
      if (!rect) continue;
      stats.validCount += 1;
      if (!isRecordVisible(record)) continue;
      stats.visibleCount += 1;

      const insideViewport = rectContains(viewport, rect);
      let coverageReason = null;
      let coveringEntry = null;

      if (insideViewport && isCullable(record, rect, index) === true) {
        coveringEntry = findContainingOccluder(
          rect,
          exactBuckets,
          largeOccluders,
          grid
        );
        if (coveringEntry) {
          coverageReason = "exact-containment";
        } else if (isCoveredByFullCells(rect, coverage, grid)) {
          coverageReason = "tile-coverage";
        }
      }

      const id = idOf(record, index);
      if (coverageReason) {
        const entry = {
          id,
          record,
          index,
          rect,
          reason: coverageReason,
          coveringId: coveringEntry ? coveringEntry.id : null,
        };
        result.occludedIds.add(id);
        result.occludedRecords.push(record);
        result.occludedEntries.push(entry);
        stats.occludedCount += 1;
        if (coverageReason === "exact-containment") {
          stats.exactContainmentCount += 1;
        } else {
          stats.tileCoverageCount += 1;
        }

        // This record will be hidden by the caller, so it must not become an
        // occluder for records below it.
        continue;
      }

      if (isOccluder(record, rect, index) !== true) continue;
      stats.eligibleOccluderCount += 1;
      const occluderEntry = { id, record, index, rect };
      addExactOccluder(
        occluderEntry,
        exactBuckets,
        largeOccluders,
        grid,
        maxExactBucketCells
      );
      fullyCoveredCellCount += markFullyCoveredCells(rect, coverage, grid);
    }

    stats.fullyCoveredCellCount = fullyCoveredCellCount;
    return result;
  }

  function createEngine(defaultOptions) {
    const defaults =
      defaultOptions && typeof defaultOptions === "object" ? defaultOptions : {};
    return {
      compute(stamps, options) {
        return compute(stamps, Object.assign({}, defaults, options || {}));
      },
    };
  }

  return Object.freeze({
    compute,
    createEngine,
    normalizeRect,
    isEligibleOccluder,
  });
});
