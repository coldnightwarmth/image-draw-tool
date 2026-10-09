#!/usr/bin/env node
import assert from 'node:assert/strict';
import { resolveRasterMemoryBudget, PHOTO_EXPORT_MEMORY_PROFILE, MAX_PHOTO_EXPORT_MEMORY_BYTES } from '../../raster-memory-budget.mjs';
const MiB = 1024 * 1024;
for (const [deviceMemoryGiB, legacy, photo] of [[undefined,384,1024],[0,384,1024],[NaN,384,1024],[.5,64,256],[1,96,256],[2,192,512],[4,384,1024],[8,768,2048],[32,768,2048]]) {
  assert.equal(resolveRasterMemoryBudget(undefined,{deviceMemoryGiB}),legacy*MiB);
  assert.equal(resolveRasterMemoryBudget(MAX_PHOTO_EXPORT_MEMORY_BYTES,{deviceMemoryGiB}),legacy*MiB,'larger requests alone cannot change existing callers');
  assert.equal(resolveRasterMemoryBudget(MAX_PHOTO_EXPORT_MEMORY_BYTES,{deviceMemoryGiB,profile:PHOTO_EXPORT_MEMORY_PROFILE}),photo*MiB);
  assert.equal(resolveRasterMemoryBudget(64*MiB,{deviceMemoryGiB,profile:PHOTO_EXPORT_MEMORY_PROFILE}),64*MiB,'explicit smaller budgets remain available');
  assert.equal(resolveRasterMemoryBudget(-1,{deviceMemoryGiB,profile:PHOTO_EXPORT_MEMORY_PROFILE}),photo*MiB);
}
assert.equal(resolveRasterMemoryBudget(Infinity,{deviceMemoryGiB:8,profile:PHOTO_EXPORT_MEMORY_PROFILE}),2048*MiB);
assert.equal(resolveRasterMemoryBudget(8*1024*MiB,{deviceMemoryGiB:8,profile:PHOTO_EXPORT_MEMORY_PROFILE}),2048*MiB);
assert.equal(resolveRasterMemoryBudget(2048*MiB,{deviceMemoryGiB:4,profile:'invalid'}),384*MiB);
console.log('Raster memory policies passed: unchanged legacy limits; 256–2048 MiB photo exports, 1024 MiB fallback.');
