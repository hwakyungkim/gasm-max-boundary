// Recomputes Table 1 and the numbers quoted in Sections 1, 3 and 5.
//
//  * M(n) for n = 2..12, as the size of the class of one boundary of B_{n,n},
//    and |A_n| by the product formula; both are compared with Table 1.
//  * The quotients M(n+1)M(n-1)/M(n)^2 for n = 10, 11 (Section 1).
//  * N(2,n) (Fibonacci numbers) and N(3,n) for n = 3..7 (Section 5).
//  * The counts in Examples 3.4-3.7: 42 and 64; 429, 897, 1322.
//
// The classes are counted directly from the definition (see gasm.mjs).
// Run with Node.js 18 or later:  node table-M.mjs        (a few seconds)
import { P, countClass, familyBoundary, familySet, asmCount, borderWalk, boundaryOfWalk, foldWalk, ringValues, key } from './gasm.mjs';

let allOk = true;
const check = (label, got, want) => {
  const ok = got === want;
  allOk &&= ok;
  console.log(`${ok ? 'OK  ' : 'FAIL'} ${label}: ${got}${ok ? '' : `  (paper: ${want})`}`);
};

// Table 1 of the paper.
const table = {
  2: [2n, 2n], 3: [7n, 7n], 4: [64n, 42n], 5: [1322n, 429n], 6: [64914n, 7436n],
  7: [7474305n, 218348n], 8: [2033739170n, 10850216n], 9: [1305583070738n, 911835460n],
  10: [1981880443295788n, 129534272700n], 11: [7111657020627320662n, 31095744852375n],
  12: [60382974032926242142168n, 12611311859677500n],
};
const minus = (n) => Array(n).fill(-1);
const M = {};
console.log('Table 1');
for (let n = 2; n <= 12; n++) {
  M[n] = countClass(...familyBoundary(n, n, 1, [1, 1, 1, 1]));
  check(`M(${n})`, M[n], table[n][0]);
  check(`|A_${n}| (product formula)`, asmCount(n), table[n][1]);
  if (n <= 9) check(`|A_${n}| (counted, classical boundary)`, countClass(minus(n), minus(n), minus(n), minus(n)), table[n][1]);
}
// All 32 boundaries of B_{n,n} give the same number (n <= 7 here).
for (let n = 3; n <= 7; n++) {
  const vals = new Set([...familySet(n, n)].map((k) => {
    const [u, u2, v, v2] = k.split('|').map(P);
    return countClass(u, u2, v, v2).toString();
  }));
  check(`all 32 boundaries of B_{${n},${n}} give one value`, vals.size, 1);
}

console.log('\nQuotients M(n+1)M(n-1)/M(n)^2 (Section 1; W^2 = 2.3703...)');
for (const n of [10, 11]) {
  const q = Number((M[n + 1] * M[n - 1] * 10n ** 6n) / (M[n] * M[n])) / 1e6;
  check(`n = ${n}`, q.toFixed(4), n === 10 ? '2.3639' : '2.3662');
}

console.log('\nN(2,n) and N(3,n) (Section 5)');
const fib = [0n, 1n, 1n]; for (let i = 3; i <= 10; i++) fib.push(fib[i - 1] + fib[i - 2]);
for (let n = 2; n <= 7; n++) check(`N(2,${n}) = Fibonacci F_${n + 1}`, countClass(...familyBoundary(2, n, 1, [1, 1, 1, 1])), fib[n + 1]);
const n3 = [7n, 17n, 41n, 99n, 239n];
for (let n = 3; n <= 7; n++) check(`N(3,${n})`, countClass(...familyBoundary(3, n, 1, [1, 1, 1, 1])), n3[n - 3]);

console.log('\nExamples');
// Example 3.4: the class has 7 - 1 = 6 elements (one ASM of order 3 is not in the image).
const b34 = [P('---'), P('-++'), P('---'), P('-++')];
check('Example 3.4: class of (---,-++|---,-++)', countClass(...b34), 6n);
// The fold of the ring profile at 2 is the ring profile of the classical boundary
// (the corner values, which play no role, may differ).
check('Example 3.4: fold at 2 gives the ring profile of the classical boundary',
  ringValues(foldWalk(borderWalk(...b34), 2)).join(','), ringValues(borderWalk(minus(3), minus(3), minus(3), minus(3))).join(','));
// Proof of Theorem 4.1: u=---, u'=+++, v=-+, v'=+- has ring profile 1,2 / 1,2 / 1 / 4 and its fold at 3 is flat.
const b41 = [P('---'), P('+++'), P('-+'), P('+-')];
const w41 = borderWalk(...b41);
check('Proof of Thm 4.1: ring profile (top, bottom, left, right)', w41 && [w41.top.slice(1, 3), w41.bottom.slice(1, 3), w41.left[1], w41.right[1]].join(' / '), '1,2 / 1,2 / 1 / 4');
check('Proof of Thm 4.1: its fold at 3 is in B_{2,3}', familySet(2, 3).has(key(...boundaryOfWalk(foldWalk(w41, 3)))), true);
check('Figure 2 boundary u=v=++-+, u\'=v\'=+-++ is in B_{4,4}', familySet(4, 4).has(key(P('++-+'), P('+-++'), P('++-+'), P('+-++'))), true);
check('Example 3.5: classical n = 4', countClass(minus(4), minus(4), minus(4), minus(4)), 42n);
const w4 = borderWalk(minus(4), minus(4), minus(4), minus(4));
check('Example 3.5: fold at 2', countClass(...boundaryOfWalk(foldWalk(w4, 2))), 64n);
const w5 = borderWalk(minus(5), minus(5), minus(5), minus(5));
const b3 = boundaryOfWalk(foldWalk(w5, 3)), b32 = boundaryOfWalk(foldWalk(foldWalk(w5, 3), 2));
check('Example 3.6: classical n = 5', countClass(minus(5), minus(5), minus(5), minus(5)), 429n);
check('Example 3.6: fold at 3', countClass(...b3), 897n);
check('Example 3.6: then fold at 2', countClass(...b32), 1322n);
check('Example 3.7: boundary after first fold', key(...b3), key(P('---++'), P('++---'), P('---++'), P('++---')));
check('Example 3.7: boundary after second fold', key(...b32), key(P('--+-+'), P('+-+--'), P('--+-+'), P('+-+--')));
check('Example 3.7: second boundary is in B_{5,5}', familySet(5, 5).has(key(...b32)), true);

console.log(allOk ? '\nAll checks passed.' : '\nSOME CHECK FAILED.');
process.exit(allOk ? 0 : 1);
