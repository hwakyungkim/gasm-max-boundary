// Exhaustive checks of Theorem 1.3, Lemma 2.1 and Theorem 3.2 on small arrays.
//
// For every size m x n in the list below and every boundary (u,u'|v,v')
// (2^(2m+2n) of them) the program counts the class directly from the
// definition and checks:
//   (1) the class is empty when the boundary is not closed (Lemma 2.1);
//   (2) the boundaries with the largest class are exactly the set B_{m,n} of
//       Definition 1.2, which has 32 elements (16 for m = n = 2) (Theorem 1.3);
//   (3) for every closed boundary and every level k, folding the border walk
//       at level k does not decrease the size of the class (Theorem 3.2).
//
// Run with Node.js 18 or later:
//   node check-max.mjs          sizes with m, n <= 4, and 2x5, 3x5, 4x5 (and transposes)
//   node check-max.mjs --big    also 5x5 (2^20 boundaries; about a minute)
import { countClass, familySet, key, borderWalk, boundaryOfWalk, foldWalk } from './gasm.mjs';

const sizes = [];
for (let m = 2; m <= 4; m++) for (let n = 2; n <= 4; n++) sizes.push([m, n]);
for (const m of [2, 3, 4]) sizes.push([m, 5], [5, m]);
if (process.argv.includes('--big')) sizes.push([5, 5]);

const bits = (k, t) => { const a = []; for (let j = 0; j < k; j++) a.push((t >> j) & 1 ? 1 : -1); return a; };

let allOk = true;
for (const [m, n] of sizes) {
  const t0 = Date.now();
  const memo = new Map();
  const count = (b) => {
    const k = key(...b);
    if (!memo.has(k)) memo.set(k, countClass(...b));
    return memo.get(k);
  };
  let max = -1n, argmax = [], openNonEmpty = 0, foldBad = 0, folds = 0;
  const N = 2 * n + 2 * m;
  for (let t = 0; t < 2 ** N; t++) {
    const u = bits(n, t), u2 = bits(n, t >> n), v = bits(m, t >> (2 * n)), v2 = bits(m, t >> (2 * n + m));
    const b = [u, u2, v, v2];
    const c = count(b);
    const w = borderWalk(...b);
    if (!w) { if (c !== 0n) openNonEmpty++; continue; }
    if (c > max) { max = c; argmax = [key(...b)]; } else if (c === max) argmax.push(key(...b));
    const all = [...w.top, ...w.bottom, ...w.left, ...w.right];
    for (let k = Math.min(...all); k <= Math.max(...all); k++) {
      folds++;
      if (count(boundaryOfWalk(foldWalk(w, k))) < c) foldBad++;
    }
  }
  const fam = familySet(m, n);
  const same = argmax.length === fam.size && argmax.every((x) => fam.has(x));
  const expected = m === 2 && n === 2 ? 16 : 32;
  const ok = same && fam.size === expected && openNonEmpty === 0 && foldBad === 0;
  allOk &&= ok;
  console.log(
    `${m}x${n}: max = ${max}, maximizers = ${argmax.length}, equal to B_{m,n}: ${same}, ` +
    `non-closed nonempty: ${openNonEmpty}, folds checked: ${folds}, folds decreasing: ${foldBad}` +
    `  [${ok ? 'OK' : 'FAIL'}] (${((Date.now() - t0) / 1000).toFixed(1)} s)`);
}
console.log(allOk ? 'All checks passed.' : 'SOME CHECK FAILED.');
process.exit(allOk ? 0 : 1);
