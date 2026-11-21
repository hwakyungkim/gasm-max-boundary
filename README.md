# The maximum of the lattice for generalized ASMs (supplementary material)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24408881.svg)](https://doi.org/10.5281/zenodo.24408881)

Supplementary material for the paper

> H. K. Kim, *The maximum of the lattice for generalized alternating sign
> matrices*, submitted to Discrete Mathematics.

The paper determines the boundaries (u,u'|v,v') for which the number of
m x n generalized alternating sign matrices is largest: for all m, n >= 2 with
(m,n) != (2,2) there are exactly 32 of them (the set B_{m,n} of Definition 1.2).

The repository contains two independent kinds of verification.

1. **Computer checks** (`*.mjs`). Plain JavaScript (ES modules); they need
   only [Node.js](https://nodejs.org) 18 or later, with no other dependencies.
   The classes are counted **directly from the definition** of a
   (u,u'|v,v')-ASM by a column-by-column transfer method, without height
   functions, so the checks do not rely on the proofs of the paper.
2. **Lean 4 formalization** (`lean/`). Machine-checked proofs of the main
   statements for all m, n >= 2; see [`lean/README.md`](lean/README.md).

## Computer checks

| File | Purpose |
|------|---------|
| `gasm.mjs` | Shared routines: the count of a class from the definition, the boundaries B_{m,n}(delta, eps) of Definition 1.2, the border walk (2), and folding. |
| `table-M.mjs` | Recomputes Table 1 (M(n) and the number of ASMs for n = 2..12), the quotients M(n+1)M(n-1)/M(n)^2 of Section 1, the values of N(2,n) and N(3,n) of Section 5, and the numbers in Examples 3.4-3.7 (6, 42, 64, 429, 897, 1322) and in the proof of Theorem 4.1. Runs in a few seconds. |
| `check-max.mjs` | For every boundary of every size m, n <= 4 and 2x5, 3x5, 4x5 (and transposes) it checks Theorem 1.3 (the maximizing boundaries are exactly B_{m,n}, 32 of them, 16 for 2x2), Lemma 2.1 (non-closed boundaries have empty classes) and the folding inequality of Theorem 3.2 at every level. With `--big` it also treats 5x5 (2^20 boundaries). |

Usage:

```
node table-M.mjs
node check-max.mjs
node check-max.mjs --big
```

Each program prints one line per check, marked `OK` or `FAIL`, and ends with
`All checks passed.` (exit code 0) or `SOME CHECK FAILED.` (exit code 1).

Boundaries are written as sign words, `+` for +1 and `-` for -1; for example
`countClass(P('---'), P('-++'), P('---'), P('-++'))` returns `6n`, the size of
the class of Example 3.4.

## Lean 4 formalization

```
cd lean
lake exe cache get     # download the compiled Mathlib
lake build
lake env lean Max32Lean/Axioms.lean
```

The main theorem (Theorem 1.3) is `ncard_gasm_le` and `ncard_gasm_eq_iff` in
`lean/Max32Lean/Gasm.lean`. Details, including what is and is not formalized,
are in [`lean/README.md`](lean/README.md).

## How to cite

H. K. Kim, *gasm-max-boundary: supplementary code and Lean formalization for
the maximum of the lattice for generalized alternating sign matrices*,
version 1.0 [software], Zenodo, 2026. https://doi.org/10.5281/zenodo.24408881

Author ORCID: https://orcid.org/0000-0001-7727-9204

## License

MIT (see `LICENSE`).
