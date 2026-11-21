/-
Prints the axioms used by the statements listed in the Introduction of the paper
"The maximum of the lattice for generalized alternating sign matrices".
Expected output for each: `propext`, `Classical.choice`, `Quot.sound` only (no `sorryAx`).
Run:  lake env lean Max32Lean/Axioms.lean
-/
import Max32Lean.Fold
import Max32Lean.Grid
import Max32Lean.Gasm
import Max32Lean.Inject

open Max32

-- Lemma 3.1
#print axioms isHeight_fold
#print axioms fold_component
#print axioms reflectOn_isHeight
-- Theorem 3.2 (inequality and strict form)
#print axioms fold_inequality
#print axioms fold_inequality_strict
-- Corollary 3.3
#print axioms phi_eq_foldLift
#print axioms phi_mem
#print axioms foldFn_phi
#print axioms phi_injOn
#print axioms phi_image
#print axioms phi_surjOn_iff
#print axioms phi_bijOn_iff
-- Theorem 4.1
#print axioms numExt_le_N
#print axioms numExt_eq_N_iff
-- Lemmas 2.1, 2.2, 2.4 and Theorem 1.3
#print axioms gasm_eq_empty_of_not_closed
#print axioms ncard_gasm
#print axioms isFlat_profile_iff
#print axioms ncard_family
#print axioms ncard_gasm_le
#print axioms ncard_gasm_eq_iff
