# Lean 4 formalization

Machine-checked proofs, in Lean 4 with Mathlib, of the main statements of
*The maximum of the lattice for generalized alternating sign matrices*.

* Lean toolchain: see `lean-toolchain` (`leanprover/lean4:v4.36.0-rc2`).
* Mathlib revision: pinned in `lake-manifest.json`.

## Building

```
lake exe cache get     # download the compiled Mathlib (recommended)
lake build
lake env lean Max32Lean/Axioms.lean
```

The last command prints the axioms used by each statement below. Every one of
them depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`: no `sorryAx` and no `native_decide`.

## Files

| File | Contents |
|------|----------|
| `Max32Lean/Fold.lean` | Folding on an arbitrary graph: Lemma 3.1 and Theorem 3.2 (inequality and strict form). |
| `Max32Lean/Inject.lean` | Corollary 3.3 (the folding injection), for an arbitrary graph and vertex set. |
| `Max32Lean/Grid.lean` | The grid graph, ring, flat ring walks, N(m,n), Theorem 4.1. |
| `Max32Lean/Gasm.lean` | Generalized ASMs with boundary (u,u'\|v,v'), Lemmas 2.1, 2.2, 2.4, and Theorem 1.3. |
| `Max32Lean/Axioms.lean` | Prints the axioms of the statements below. |

## Statements of the paper and their Lean names

| Paper | Lean |
|-------|------|
| Lemma 3.1 (a), (b), (c) | `isHeight_fold`, `fold_component`, `reflectOn_isHeight` |
| Theorem 3.2, inequality and strict form | `fold_inequality`, `fold_inequality_strict` |
| Corollary 3.3 | `phi_eq_foldLift`, `phi_mem`, `foldFn_phi`, `phi_injOn`, `phi_image`, `phi_surjOn_iff`, `phi_bijOn_iff` |
| Theorem 4.1 | `numExt_le_N`, `numExt_eq_N_iff` |
| Lemma 2.1 (count only) | `gasm_eq_empty_of_not_closed`, `ncard_gasm` |
| Lemma 2.4 and the count of B_{m,n} | `isFlat_profile_iff`, `ncard_family` |
| **Theorem 1.3** | **`ncard_gasm_le`, `ncard_gasm_eq_iff`** |

```
theorem ncard_gasm_le     : (gasm b).ncard ≤ N m n
theorem ncard_gasm_eq_iff : (gasm b).ncard = N m n ↔ InFamily b
```

for all m, n >= 2 and every boundary `b` with entries ±1.

## Not formalized

As stated in the Introduction of the paper, the following are not formalized:
the fibre formulas (3) of Theorem 3.2, the statements about the Bruhat order
(the order part of Lemmas 2.1 and 2.2, Corollary 5.2), the examples, and
Table 1. Four declarations are stated with `sorry` for this reason, and Lean
reports "declaration uses 'sorry'" for them; none of them is used in the proofs
above (this is what `Axioms.lean` confirms):

* `fibre_formula_fold`, `fibre_formula` (`Fold.lean`): the fibre formulas (3);
* `N_table`, `N_two` (`Grid.lean`): numerical values of N(m,n). These values are
  checked by the program `table-M.mjs` instead.

The proof of Theorem 3.2 in Lean obtains the inequality directly from the
injection of Corollary 3.3, without the fibre formulas.

## What a Lean proof certifies

Lean checks that the theorems follow from the definitions in these files. That
the definitions (`gasm`, `InFamily`, `Alternates`, ...) express what the paper
says has to be checked by reading them; they are short and are found at the
beginning of `Gasm.lean` and `Grid.lean`.
