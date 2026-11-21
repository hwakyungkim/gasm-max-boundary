// Shared routines for "The maximum of the lattice for generalized alternating
// sign matrices" (H. K. Kim).
//
// The count |A_{m,n}(u,u'|v,v')| is computed directly from the definition of a
// (u,u'|v,v')-ASM (alternation in every row and column of the bordered array),
// with no use of height functions, so that the programs check the paper
// independently of its proofs.
//
// Conventions: sign vectors are arrays of +1/-1, indexed from 0 in code; the
// paper indexes them from 1.  P('+-+') = [1,-1,1].

export const P = (w) => [...w].map((c) => (c === '+' ? 1 : -1));
export const W = (a) => a.map((x) => (x > 0 ? '+' : '-')).join('');

// Number of m x n (0,+-1)-matrices A such that every row and every column of
// the bordered array A(u,u'|v,v') alternates in sign (zeros ignored).
//
// Column-by-column transfer: the state is, for each row i, the last nonzero
// sign of row i seen so far (initially v_i), stored as a bit mask
// (bit i = 1 iff that sign is +1).  A nonzero entry in row i must be the
// negative of the state of row i.  In column j the nonzero entries, read from
// top to bottom, must start with -u_j, alternate, and end with -u'_j (or be
// absent when u'_j = -u_j).  At the end row i must have last sign -v'_i.
export function countClass(u, u2, v, v2) {
  const n = u.length, m = v.length;
  let init = 0;
  for (let i = 0; i < m; i++) if (v[i] > 0) init |= 1 << i;
  let cur = new Map([[init, 1n]]);
  for (let j = 0; j < n; j++) {
    const next = new Map();
    for (const [s, c] of cur) {
      // DFS over rows; e = the sign required for the next nonzero entry.
      const dfs = (i, e, t) => {
        if (i === m) {
          if (e === u2[j]) next.set(t, (next.get(t) || 0n) + c);
          return;
        }
        dfs(i + 1, e, t);                                  // entry 0
        const x = (s >> i) & 1 ? -1 : 1;                   // forced sign in row i
        if (x === e) dfs(i + 1, -e, t ^ (1 << i));         // entry x
      };
      dfs(0, -u[j], s);
    }
    cur = next;
  }
  let fin = 0;
  for (let i = 0; i < m; i++) if (-v2[i] > 0) fin |= 1 << i;
  return cur.get(fin) || 0n;
}

// The boundary B_{m,n}(delta, eps) of Definition 1.2 (eps = [e1,e2,e3,e4]).
// Returns [u, u', v, v'].
export function familyBoundary(m, n, delta, eps) {
  const u = [], u2 = [], v = [], v2 = [];
  for (let j = 1; j <= n; j++) {
    u.push(delta * (-1) ** j);
    u2.push(delta * (-1) ** (j + m + 1));
  }
  for (let i = 1; i <= m; i++) {
    v.push(delta * (-1) ** i);
    v2.push(delta * (-1) ** (i + n + 1));
  }
  const [e1, e2, e3, e4] = eps;
  u[0] = v[0] = e1;            // top left
  u[n - 1] = v2[0] = e2;       // top right
  u2[0] = v[m - 1] = e3;       // bottom left
  u2[n - 1] = v2[m - 1] = e4;  // bottom right
  return [u, u2, v, v2];
}

// The set B_{m,n} as a set of keys "u|u'|v|v'".
export function familySet(m, n) {
  const S = new Set();
  for (const d of [1, -1])
    for (let t = 0; t < 16; t++) {
      const eps = [0, 1, 2, 3].map((b) => ((t >> b) & 1 ? -1 : 1));
      S.add(key(...familyBoundary(m, n, d, eps)));
    }
  return S;
}

export const key = (u, u2, v, v2) => [u, u2, v, v2].map(W).join('|');

// Border walk (2) of the paper.  Returns null if the boundary is not closed,
// otherwise {top, bottom, left, right}: top[j] = phi(0,j), bottom[j] = phi(m,j)
// (j = 0..n), left[i] = phi(i,0), right[i] = phi(i,n) (i = 0..m).
export function borderWalk(u, u2, v, v2) {
  const n = u.length, m = v.length;
  const top = [0], left = [0];
  for (let j = 1; j <= n; j++) top.push(top[j - 1] - u[j - 1]);
  for (let i = 1; i <= m; i++) left.push(left[i - 1] - v[i - 1]);
  const bottom = [left[m]], right = [top[n]];
  for (let j = 1; j <= n; j++) bottom.push(bottom[j - 1] + u2[j - 1]);
  for (let i = 1; i <= m; i++) right.push(right[i - 1] + v2[i - 1]);
  if (bottom[n] !== right[m]) return null;
  return { top, bottom, left, right };
}

// Inverse of borderWalk.
export function boundaryOfWalk(w) {
  const { top, bottom, left, right } = w;
  const n = top.length - 1, m = left.length - 1;
  const u = [], u2 = [], v = [], v2 = [];
  for (let j = 1; j <= n; j++) { u.push(top[j - 1] - top[j]); u2.push(bottom[j] - bottom[j - 1]); }
  for (let i = 1; i <= m; i++) { v.push(left[i - 1] - left[i]); v2.push(right[i] - right[i - 1]); }
  return [u, u2, v, v2];
}

// Values of the ring profile (border walk without the four corners).
export function ringValues(w) {
  const { top, bottom, left, right } = w;
  const n = top.length - 1, m = left.length - 1;
  return [...top.slice(1, n), ...bottom.slice(1, n), ...left.slice(1, m), ...right.slice(1, m)];
}

// Fold F_k x = k - |x - k| applied to the whole border walk (as in Example 3.7).
export function foldWalk(w, k) {
  const F = (a) => a.map((x) => k - Math.abs(x - k));
  return { top: F(w.top), bottom: F(w.bottom), left: F(w.left), right: F(w.right) };
}

// Number of n x n alternating sign matrices.
export function asmCount(n) {
  let num = 1n, den = 1n;
  const fact = (k) => { let r = 1n; for (let i = 2n; i <= BigInt(k); i++) r *= i; return r; };
  for (let k = 0; k < n; k++) { num *= fact(3 * k + 1); den *= fact(n + k); }
  return num / den;
}
