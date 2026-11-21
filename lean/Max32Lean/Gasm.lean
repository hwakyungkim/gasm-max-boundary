/-
Part C of `aristotle_request.md`: generalized alternating sign matrices.
Paper: gasm_32_06, Sections 1 and 2 (Definition 1.2, Lemmas 2.1, 2.2, 2.4, Theorem 1.3).

Status: C1–C4 are proved; this file has no `sorry`. The main theorem is `ncard_gasm_le` and
`ncard_gasm_eq_iff` at the end of the file.

Plan of the proofs. A bordered row or column alternates iff its partial sums stay in two values
(`alternates_iff`). So `A` is in the class iff all steps of `h_A` are `±1` and the steps along the
bottom and right sides are `u'` and `v'` (`mem_gasm_iff_steps`). This gives Lemma 2.1
(`gasm_height`, `heightOf_bijOn`), then Lemma 2.2 by restriction to `Γ` (`restrict_bijOn`).
Lemma 2.4 is `family_values` (one direction) and `inFamily_of_isFlat` (the other).

Indices: the paper counts from 1, Lean's `Fin` counts from 0. The paper's `u_j` is `b.u j'` with
`j'.val = j - 1`. So "`2 ≤ j ≤ n - 1`" becomes `1 ≤ j'.val ∧ j'.val + 2 ≤ n`, and the exponent `j`
becomes `j'.val + 1`.
-/
import Mathlib
import Max32Lean.Fold
import Max32Lean.Grid

open BigOperators

namespace Max32

/-! ### Alternating sequences -/

/-- No two consecutive terms are equal. -/
def NoRepeat : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => a ≠ b ∧ NoRepeat (b :: l)

/-- A sequence alternates if, after deleting its zero terms, no two consecutive terms are equal. -/
def Alternates (l : List ℤ) : Prop :=
  NoRepeat (l.filter fun x => decide (x ≠ 0))

/-! ### Boundaries and classes -/

/-- A boundary `(u, u' | v, v')` of an `m × n` array. -/
@[ext] structure Bdry (m n : ℕ) where
  u : Fin n → ℤ
  u' : Fin n → ℤ
  v : Fin m → ℤ
  v' : Fin m → ℤ

variable {m n : ℕ}

def IsSign (x : ℤ) : Prop := x = 1 ∨ x = -1

/-- All boundary entries are `±1`. -/
def Bdry.IsSigns (b : Bdry m n) : Prop :=
  (∀ j, IsSign (b.u j)) ∧ (∀ j, IsSign (b.u' j)) ∧ (∀ i, IsSign (b.v i)) ∧ (∀ i, IsSign (b.v' i))

/-- The class `𝒜_{m,n}(u,u'|v,v')`: the `(0,±1)`-matrices whose bordered rows and columns
alternate. -/
def gasm (b : Bdry m n) : Set (Matrix (Fin m) (Fin n) ℤ) :=
  {A | (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) ∧
    (∀ i, Alternates ((b.v i :: List.ofFn fun j => A i j) ++ [b.v' i])) ∧
    (∀ j, Alternates ((b.u j :: List.ofFn fun i => A i j) ++ [b.u' j]))}

/-- The family `ℬ_{m,n}` (Definition 1.2). -/
def InFamily (b : Bdry m n) : Prop :=
  b.IsSigns ∧ ∃ δ : ℤ, IsSign δ ∧
    (∀ j : Fin n, 1 ≤ j.val → j.val + 2 ≤ n →
      b.u j = δ * (-1) ^ (j.val + 1) ∧ b.u' j = δ * (-1) ^ (j.val + 1 + m + 1)) ∧
    (∀ i : Fin m, 1 ≤ i.val → i.val + 2 ≤ m →
      b.v i = δ * (-1) ^ (i.val + 1) ∧ b.v' i = δ * (-1) ^ (i.val + 1 + n + 1)) ∧
    (∀ (j : Fin n) (i : Fin m), j.val = 0 → i.val = 0 → b.u j = b.v i) ∧
    (∀ (j : Fin n) (i : Fin m), j.val + 1 = n → i.val = 0 → b.u j = b.v' i) ∧
    (∀ (j : Fin n) (i : Fin m), j.val = 0 → i.val + 1 = m → b.u' j = b.v i) ∧
    (∀ (j : Fin n) (i : Fin m), j.val + 1 = n → i.val + 1 = m → b.u' j = b.v' i)

/-! ### The border walk -/

/-- The sum of the first `t` entries of `w`. -/
def psum {k : ℕ} (w : Fin k → ℤ) (t : ℕ) : ℤ :=
  ∑ l : Fin k, if l.val < t then w l else 0

/-- The boundary is closed: the two values of the border walk at `(m,n)` agree. -/
def Bdry.Closed (b : Bdry m n) : Prop :=
  -psum b.v m + psum b.u' n = -psum b.u n + psum b.v' m

/-- The border walk `φ` (equation (2) of the paper), as a function on the whole grid.
Only its values on the border are used. -/
def borderWalk (b : Bdry m n) (p : Pt m n) : ℤ :=
  if p.1.val = 0 then -psum b.u p.2.val
  else if p.2.val = 0 then -psum b.v p.1.val
  else if p.1.val = m then -psum b.v m + psum b.u' p.2.val
  else -psum b.u n + psum b.v' p.1.val

/-- The ring profile `ρ = φ|_R`. -/
def profile (b : Bdry m n) : nonCorner m n → ℤ := fun p => borderWalk b p.1

/-- `σ_{ij}(A)`: the sum of the entries in the first `i` rows and first `j` columns. -/
def sumMatrix (A : Matrix (Fin m) (Fin n) ℤ) (i j : ℕ) : ℤ :=
  ∑ a : Fin m, ∑ c : Fin n, if a.val < i ∧ c.val < j then A a c else 0

/-- The height function `h_A` of a matrix (Lemma 2.1). -/
def heightOf (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ) : Pt m n → ℤ :=
  fun p => -psum b.u p.2.val - psum b.v p.1.val - 2 * sumMatrix A p.1.val p.2.val

/-! ### Partial sums -/

theorem psum_zero {k : ℕ} (w : Fin k → ℤ) : psum w 0 = 0 := by
  simp [psum]

theorem psum_step {k : ℕ} (w : Fin k → ℤ) (t : ℕ) (ht : t < k) :
    psum w (t + 1) = psum w t + w ⟨t, ht⟩ := by
  unfold psum
  have h : ∀ l : Fin k, (if l.val < t + 1 then w l else 0) =
      (if l.val < t then w l else 0) + (if l = ⟨t, ht⟩ then w l else 0) := by
    intro l
    by_cases h1 : l.val < t
    · have h2 : l ≠ ⟨t, ht⟩ := by
        intro e
        rw [e] at h1
        exact lt_irrefl _ h1
      have h3 : l.val < t + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : l = ⟨t, ht⟩
      · subst h2
        simp
      · have h3 : ¬ l.val < t + 1 := by
          intro h
          apply h2
          apply Fin.ext
          show l.val = t
          omega
        simp [h1, h2, h3]
  rw [Finset.sum_congr rfl (fun l _ => h l), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem psum_succ {k : ℕ} (f : Fin (k + 1) → ℤ) (t : ℕ) :
    psum f (t + 1) = f 0 + psum (fun i => f i.succ) t := by
  simp [psum, Fin.sum_univ_succ]

theorem sumMatrix_rows (A : Matrix (Fin m) (Fin n) ℤ) (i j : ℕ) :
    sumMatrix A i j = psum (fun a => psum (fun c => A a c) j) i := by
  unfold sumMatrix psum
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : a.val < i <;> simp [h]

theorem sumMatrix_cols (A : Matrix (Fin m) (Fin n) ℤ) (i j : ℕ) :
    sumMatrix A i j = psum (fun c => psum (fun a => A a c) i) j := by
  unfold sumMatrix psum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h : c.val < j <;> simp [h]

/-! ### Alternation in terms of partial sums -/

theorem isSign_neg {x : ℤ} : IsSign (-x) ↔ IsSign x := by
  unfold IsSign
  omega

theorem alt_cons_zero (s : ℤ) (l : List ℤ) : Alternates (s :: 0 :: l) ↔ Alternates (s :: l) := by
  simp [Alternates, List.filter]

theorem alt_cons_cons {s a : ℤ} (hs : s ≠ 0) (ha : a ≠ 0) (l : List ℤ) :
    Alternates (s :: a :: l) ↔ s ≠ a ∧ Alternates (a :: l) := by
  simp [Alternates, List.filter, hs, ha, NoRepeat]

theorem alt_pair {s s' : ℤ} (hs : s ≠ 0) (hs' : s' ≠ 0) : Alternates [s, s'] ↔ s ≠ s' := by
  simp [Alternates, List.filter, hs, hs', NoRepeat]

/-- The bordered sequence `s, f 0, …, f (k-1), s'` alternates iff every partial sum of `f` is `0`
or `-s`, and the total is `-s` if `s' = s` and `0` if `s' = -s` (proof of Lemma 2.1). -/
theorem alternates_iff : ∀ (k : ℕ) (f : Fin k → ℤ), (∀ j, f j = 0 ∨ f j = 1 ∨ f j = -1) →
    ∀ s s' : ℤ, IsSign s → IsSign s' →
    (Alternates ((s :: List.ofFn f) ++ [s']) ↔
      (∀ t, t ≤ k → IsSign (s + 2 * psum f t)) ∧ s + 2 * psum f k = -s') := by
  intro k
  induction k with
  | zero =>
    intro f _ s s' hs hs'
    have hs0 : s ≠ 0 := by unfold IsSign at hs; omega
    have hs0' : s' ≠ 0 := by unfold IsSign at hs'; omega
    rw [List.ofFn_zero]
    show Alternates [s, s'] ↔ _
    rw [alt_pair hs0 hs0', psum_zero]
    constructor
    · intro hne
      refine ⟨fun t _ => ?_, ?_⟩
      · have ht : psum f t = 0 := by simp [psum]
        rw [ht]
        simpa using hs
      · unfold IsSign at hs hs'
        omega
    · rintro ⟨-, h2⟩
      unfold IsSign at hs hs'
      omega
  | succ k ih =>
    intro f hf s s' hs hs'
    have hs0 : s ≠ 0 := by unfold IsSign at hs; omega
    have ih' := ih (fun i => f i.succ) (fun j => hf j.succ)
    rw [List.ofFn_succ]
    have hsplit : ((∀ t, t ≤ k + 1 → IsSign (s + 2 * psum f t)) ∧
        s + 2 * psum f (k + 1) = -s') ↔
        ((∀ t, t ≤ k → IsSign (s + 2 * f 0 + 2 * psum (fun i => f i.succ) t)) ∧
          s + 2 * f 0 + 2 * psum (fun i => f i.succ) k = -s') := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun t ht => ?_, ?_⟩
        · have h3 := h1 (t + 1) (by omega)
          rw [psum_succ] at h3
          have e : s + 2 * (f 0 + psum (fun i => f i.succ) t) =
              s + 2 * f 0 + 2 * psum (fun i => f i.succ) t := by ring
          rw [e] at h3
          exact h3
        · rw [psum_succ] at h2
          linarith
      · rintro ⟨h1, h2⟩
        refine ⟨fun t ht => ?_, ?_⟩
        · cases t with
          | zero =>
            rw [psum_zero]
            simpa using hs
          | succ t =>
            rw [psum_succ]
            have h3 := h1 t (by omega)
            have e : s + 2 * (f 0 + psum (fun i => f i.succ) t) =
                s + 2 * f 0 + 2 * psum (fun i => f i.succ) t := by ring
            rw [e]
            exact h3
        · rw [psum_succ]
          linarith
    rw [hsplit]
    by_cases h0 : f 0 = 0
    · rw [h0]
      show Alternates (s :: 0 :: (List.ofFn (fun i => f i.succ) ++ [s'])) ↔ _
      rw [alt_cons_zero]
      have e := ih' s s' hs hs'
      have e' : Alternates (s :: (List.ofFn (fun i => f i.succ) ++ [s'])) ↔
          Alternates ((s :: List.ofFn fun i => f i.succ) ++ [s']) := Iff.rfl
      rw [e', e]
      simp
    · have ha : IsSign (f 0) := by
        rcases hf 0 with h | h | h
        · exact absurd h h0
        · exact Or.inl h
        · exact Or.inr h
      show Alternates (s :: f 0 :: (List.ofFn (fun i => f i.succ) ++ [s'])) ↔ _
      rw [alt_cons_cons hs0 h0]
      have e := ih' (f 0) s' ha hs'
      have e' : Alternates (f 0 :: (List.ofFn (fun i => f i.succ) ++ [s'])) ↔
          Alternates ((f 0 :: List.ofFn fun i => f i.succ) ++ [s']) := Iff.rfl
      rw [e', e]
      by_cases hne : s = f 0
      · constructor
        · rintro ⟨h, -⟩
          exact absurd hne h
        · rintro ⟨h1, -⟩
          have h3 := h1 0 (Nat.zero_le _)
          rw [psum_zero] at h3
          unfold IsSign at h3 hs ha
          omega
      · have e2 : s + 2 * f 0 = f 0 := by
          unfold IsSign at hs ha
          omega
        rw [e2]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · intro h
          exact ⟨hne, h⟩

/-- Membership in a class, in terms of partial sums of rows and columns. -/
theorem mem_gasm_iff (b : Bdry m n) (hb : b.IsSigns) (A : Matrix (Fin m) (Fin n) ℤ) :
    A ∈ gasm b ↔ (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) ∧
      (∀ i : Fin m, (∀ t, t ≤ n → IsSign (b.v i + 2 * psum (fun c => A i c) t)) ∧
        b.v i + 2 * psum (fun c => A i c) n = -b.v' i) ∧
      (∀ j : Fin n, (∀ t, t ≤ m → IsSign (b.u j + 2 * psum (fun a => A a j) t)) ∧
        b.u j + 2 * psum (fun a => A a j) m = -b.u' j) := by
  obtain ⟨hu, hu', hv, hv'⟩ := hb
  constructor
  · rintro ⟨he, hr, hcol⟩
    exact ⟨he,
      fun i => (alternates_iff n (fun c => A i c) (he i) _ _ (hv i) (hv' i)).mp (hr i),
      fun j => (alternates_iff m (fun a => A a j) (fun a => he a j) _ _ (hu j) (hu' j)).mp
        (hcol j)⟩
  · rintro ⟨he, hr, hcol⟩
    exact ⟨he,
      fun i => (alternates_iff n (fun c => A i c) (he i) _ _ (hv i) (hv' i)).mpr (hr i),
      fun j => (alternates_iff m (fun a => A a j) (fun a => he a j) _ _ (hu j) (hu' j)).mpr
        (hcol j)⟩

/-! ### The steps of `h_A` -/

/-- `h_A` with natural-number coordinates. -/
def hval (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ) (i j : ℕ) : ℤ :=
  -psum b.u j - psum b.v i - 2 * sumMatrix A i j

theorem hval_hstep (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ) (i c : ℕ) (hc : c < n) :
    hval b A i (c + 1) - hval b A i c =
      -(b.u ⟨c, hc⟩ + 2 * psum (fun a => A a ⟨c, hc⟩) i) := by
  unfold hval
  rw [sumMatrix_cols, sumMatrix_cols, psum_step b.u c hc,
    psum_step (fun c => psum (fun a => A a c) i) c hc]
  ring

theorem hval_vstep (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ) (a t : ℕ) (ha : a < m) :
    hval b A (a + 1) t - hval b A a t =
      -(b.v ⟨a, ha⟩ + 2 * psum (fun c => A ⟨a, ha⟩ c) t) := by
  unfold hval
  rw [sumMatrix_rows, sumMatrix_rows, psum_step b.v a ha,
    psum_step (fun a => psum (fun c => A a c) t) a ha]
  ring

/-- Membership in a class, in terms of the steps of `h_A`: every step is `±1`, the steps along
the bottom side are `u'` and the steps along the right side are `v'`. -/
theorem mem_gasm_iff_steps (b : Bdry m n) (hb : b.IsSigns) (A : Matrix (Fin m) (Fin n) ℤ) :
    A ∈ gasm b ↔ (∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) ∧
      (∀ i, i ≤ m → ∀ c, c < n → IsSign (hval b A i (c + 1) - hval b A i c)) ∧
      (∀ a, a < m → ∀ t, t ≤ n → IsSign (hval b A (a + 1) t - hval b A a t)) ∧
      (∀ c (hc : c < n), hval b A m (c + 1) - hval b A m c = b.u' ⟨c, hc⟩) ∧
      (∀ a (ha : a < m), hval b A (a + 1) n - hval b A a n = b.v' ⟨a, ha⟩) := by
  rw [mem_gasm_iff b hb]
  constructor
  · rintro ⟨he, hr, hcol⟩
    refine ⟨he, ?_, ?_, ?_, ?_⟩
    · intro i hi c hc
      rw [hval_hstep b A i c hc]
      exact isSign_neg.mpr ((hcol ⟨c, hc⟩).1 i hi)
    · intro a ha t ht
      rw [hval_vstep b A a t ha]
      exact isSign_neg.mpr ((hr ⟨a, ha⟩).1 t ht)
    · intro c hc
      rw [hval_hstep b A m c hc]
      have := (hcol ⟨c, hc⟩).2
      linarith
    · intro a ha
      rw [hval_vstep b A a n ha]
      have := (hr ⟨a, ha⟩).2
      linarith
  · rintro ⟨he, f1, f2, f3, f4⟩
    refine ⟨he, fun a => ⟨fun t ht => ?_, ?_⟩, fun c => ⟨fun t ht => ?_, ?_⟩⟩
    · have h := f2 a.val a.isLt t ht
      rw [hval_vstep b A a.val t a.isLt] at h
      exact isSign_neg.mp h
    · have h := f4 a.val a.isLt
      rw [hval_vstep b A a.val n a.isLt] at h
      linarith
    · have h := f1 t ht c.val c.isLt
      rw [hval_hstep b A t c.val c.isLt] at h
      exact isSign_neg.mp h
    · have h := f3 c.val c.isLt
      rw [hval_hstep b A m c.val c.isLt] at h
      linarith

/-! ### Height functions on the grid -/

/-- Adjacency in the grid `G` in coordinates. -/
theorem grid_adj_iff (p q : Pt m n) :
    (gridGraph m n).Adj p q ↔
      (p.1.val = q.1.val ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
      (p.2.val = q.2.val ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val)) := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  obtain ⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩ := q
  unfold gridGraph
  rw [SimpleGraph.fromRel_adj]
  simp only [ne_eq, Prod.mk.injEq, Fin.mk.injEq]
  omega

theorem isSign_iff_abs {x : ℤ} : IsSign x ↔ |x| = 1 :=
  (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).symm

/-- A function on the grid whose horizontal and vertical steps are `±1` is a height function. -/
theorem isHeight_grid_of_steps (H : ℕ → ℕ → ℤ)
    (h1 : ∀ i, i ≤ m → ∀ c, c < n → IsSign (H i (c + 1) - H i c))
    (h2 : ∀ a, a < m → ∀ t, t ≤ n → IsSign (H (a + 1) t - H a t)) :
    IsHeight (gridGraph m n) (fun p => H p.1.val p.2.val) := by
  intro p q hpq
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  have hq1 := q.1.isLt
  have hq2 := q.2.isLt
  show |H p.1.val p.2.val - H q.1.val q.2.val| = 1
  rcases (grid_adj_iff p q).mp hpq with ⟨e, h | h⟩ | ⟨e, h | h⟩
  · rw [← e, ← h, abs_sub_comm]
    exact isSign_iff_abs.mp (h1 _ (by omega) _ (by omega))
  · rw [e, ← h]
    exact isSign_iff_abs.mp (h1 _ (by omega) _ (by omega))
  · rw [← e, ← h, abs_sub_comm]
    exact isSign_iff_abs.mp (h2 _ (by omega) _ (by omega))
  · rw [e, ← h]
    exact isSign_iff_abs.mp (h2 _ (by omega) _ (by omega))

/-- The grid vertex `(min i m, min j n)`; it is `(i,j)` when `i ≤ m` and `j ≤ n`. -/
def cl {m n : ℕ} (i j : ℕ) : Pt m n := (⟨min i m, by omega⟩, ⟨min j n, by omega⟩)

theorem cl_self (p : Pt m n) : cl p.1.val p.2.val = p := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · show min i m = i
    omega
  · show min j n = j
    omega

/-! ### The border walk on the four sides -/

theorem bw_top (b : Bdry m n) (p : Pt m n) (h : p.1.val = 0) :
    borderWalk b p = -psum b.u p.2.val := by
  unfold borderWalk
  split_ifs
  rfl

theorem bw_left (b : Bdry m n) (p : Pt m n) (h : p.2.val = 0) :
    borderWalk b p = -psum b.v p.1.val := by
  unfold borderWalk
  split_ifs with a1
  · rw [h, a1, psum_zero, psum_zero]
  · rfl

theorem bw_bottom (hm : 1 ≤ m) (b : Bdry m n) (p : Pt m n) (h : p.1.val = m) :
    borderWalk b p = -psum b.v m + psum b.u' p.2.val := by
  unfold borderWalk
  split_ifs with a1 a2
  · omega
  · rw [a2, h, psum_zero]
    ring
  · rfl

theorem bw_right (hn : 1 ≤ n) (b : Bdry m n) (hc : b.Closed) (p : Pt m n) (h : p.2.val = n) :
    borderWalk b p = -psum b.u n + psum b.v' p.1.val := by
  unfold borderWalk
  split_ifs with a1 a2 a3
  · rw [h, a1, psum_zero]
    ring
  · omega
  · rw [h, a3]
    exact hc
  · rfl

/-! ### `h_A` on the border -/

theorem hval_top (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ) (j : ℕ) :
    hval b A 0 j = -psum b.u j := by
  unfold hval
  rw [sumMatrix_rows, psum_zero, psum_zero]
  ring

theorem hval_left (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ) (i : ℕ) :
    hval b A i 0 = -psum b.v i := by
  unfold hval
  rw [sumMatrix_cols, psum_zero, psum_zero]
  ring

theorem hval_bottom (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ)
    (f3 : ∀ c (hc : c < n), hval b A m (c + 1) - hval b A m c = b.u' ⟨c, hc⟩) :
    ∀ j, j ≤ n → hval b A m j = -psum b.v m + psum b.u' j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [hval_left, psum_zero]
    ring
  | succ j ih =>
    intro hj
    have h1 := f3 j (by omega)
    have h2 := ih (by omega)
    rw [psum_step b.u' j (by omega)]
    linarith

theorem hval_right (b : Bdry m n) (A : Matrix (Fin m) (Fin n) ℤ)
    (f4 : ∀ a (ha : a < m), hval b A (a + 1) n - hval b A a n = b.v' ⟨a, ha⟩) :
    ∀ i, i ≤ m → hval b A i n = -psum b.u n + psum b.v' i := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hval_top, psum_zero]
    ring
  | succ i ih =>
    intro hi
    have h1 := f4 i (by omega)
    have h2 := ih (by omega)
    rw [psum_step b.v' i (by omega)]
    linarith

/-- For a matrix of the class, the boundary is closed and `h_A` is a height function on `G` that
agrees with the border walk on the border. -/
theorem gasm_height (hm : 1 ≤ m) (hn : 1 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (A : Matrix (Fin m) (Fin n) ℤ) (hA : A ∈ gasm b) :
    b.Closed ∧ IsHeight (gridGraph m n) (heightOf b A) ∧
      ∀ p, IsBorder m n p → heightOf b A p = borderWalk b p := by
  obtain ⟨-, f1, f2, f3, f4⟩ := (mem_gasm_iff_steps b hb A).mp hA
  have hB := hval_bottom b A f3
  have hR := hval_right b A f4
  have hcl : b.Closed := by
    have h1 := hB n le_rfl
    have h2 := hR m le_rfl
    unfold Bdry.Closed
    linarith
  refine ⟨hcl, isHeight_grid_of_steps (hval b A) f1 f2, ?_⟩
  intro p hp
  have hp1 := p.1.isLt
  have hp2 := p.2.isLt
  show hval b A p.1.val p.2.val = borderWalk b p
  rcases hp with h | h | h | h
  · rw [bw_top b p h, h, hval_top]
  · rw [bw_bottom hm b p h, h]
    exact hB _ (by omega)
  · rw [bw_left b p h, h, hval_left]
  · rw [bw_right hn b hcl p h, h]
    exact hR _ (by omega)

/-! ### The matrix of a height function -/

/-- The matrix with `2 a_{ij} = -(second difference of H)`. -/
def matOf (H : ℕ → ℕ → ℤ) : Matrix (Fin m) (Fin n) ℤ := fun a c =>
  (H a.val (c.val + 1) - H a.val c.val - (H (a.val + 1) (c.val + 1) - H (a.val + 1) c.val)) / 2

theorem matOf_two (H : ℕ → ℕ → ℤ)
    (h1 : ∀ i, i ≤ m → ∀ c, c < n → IsSign (H i (c + 1) - H i c))
    (a c : ℕ) (ha : a < m) (hc : c < n) :
    2 * (matOf H : Matrix (Fin m) (Fin n) ℤ) ⟨a, ha⟩ ⟨c, hc⟩ =
      H a (c + 1) - H a c - (H (a + 1) (c + 1) - H (a + 1) c) := by
  have s1 := h1 a (by omega) c hc
  have s2 := h1 (a + 1) (by omega) c hc
  show 2 * ((H a (c + 1) - H a c - (H (a + 1) (c + 1) - H (a + 1) c)) / 2) = _
  unfold IsSign at s1 s2
  omega

theorem matOf_col (H : ℕ → ℕ → ℤ)
    (h1 : ∀ i, i ≤ m → ∀ c, c < n → IsSign (H i (c + 1) - H i c)) (c : ℕ) (hc : c < n) :
    ∀ i, i ≤ m → 2 * psum (fun a => (matOf H : Matrix (Fin m) (Fin n) ℤ) a ⟨c, hc⟩) i =
      H 0 (c + 1) - H 0 c - (H i (c + 1) - H i c) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [psum_zero]
    ring
  | succ i ih =>
    intro hi
    have h2 := ih (by omega)
    have h3 := matOf_two H h1 i c (by omega) hc
    rw [psum_step (fun a => (matOf H : Matrix (Fin m) (Fin n) ℤ) a ⟨c, hc⟩) i (by omega)]
    linarith

/-- If `H` has steps `±1` along the rows and is the border walk on the top and left sides, then
`h_A = H` for `A = matOf H`. -/
theorem hval_matOf (b : Bdry m n) (H : ℕ → ℕ → ℤ)
    (h1 : ∀ i, i ≤ m → ∀ c, c < n → IsSign (H i (c + 1) - H i c))
    (htop : ∀ j, j ≤ n → H 0 j = -psum b.u j) (hleft : ∀ i, i ≤ m → H i 0 = -psum b.v i)
    (i : ℕ) (hi : i ≤ m) : ∀ j, j ≤ n → hval b (matOf H) i j = H i j := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [hval_left, hleft i hi]
  | succ c ih =>
    intro hj
    have hc : c < n := by omega
    have e1 := hval_hstep b (matOf H) i c hc
    have e2 := matOf_col H h1 c hc i hi
    have e3 := htop (c + 1) hj
    have e4 := htop c (by omega)
    have e5 := ih (by omega)
    rw [psum_step b.u c hc] at e3
    linarith

/-! ### The statements -/

/-- **C1 (Lemma 2.1), first part.** A boundary that is not closed has an empty class. -/
theorem gasm_eq_empty_of_not_closed (hm : 1 ≤ m) (hn : 1 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (hc : ¬ b.Closed) : gasm b = ∅ := by
  by_contra hne
  obtain ⟨A, hA⟩ := Set.nonempty_iff_ne_empty.mpr hne
  exact hc (gasm_height hm hn b hb A hA).1

/-- **C1 (Lemma 2.1), second part.** `A ↦ h_A` is a bijection from the class onto the height
functions on `G` that agree with `φ` on the border. -/
theorem heightOf_bijOn (hm : 1 ≤ m) (hn : 1 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (hc : b.Closed) :
    Set.BijOn (heightOf b) (gasm b)
      {h | IsHeight (gridGraph m n) h ∧ ∀ p, IsBorder m n p → h p = borderWalk b p} := by
  refine ⟨fun A hA => (gasm_height hm hn b hb A hA).2, ?_, ?_⟩
  · -- injective: the entries are second differences of `h_A`
    intro A _ A' _ heq
    have hv : ∀ i j, i ≤ m → j ≤ n → hval b A i j = hval b A' i j := by
      intro i j hi hj
      exact congrFun heq (⟨i, by omega⟩, ⟨j, by omega⟩)
    ext a c
    obtain ⟨a, ha⟩ := a
    obtain ⟨c, hc'⟩ := c
    have e1 : 2 * A ⟨a, ha⟩ ⟨c, hc'⟩ =
        -(hval b A (a + 1) (c + 1) - hval b A a (c + 1)) + (hval b A (a + 1) c - hval b A a c) := by
      rw [hval_vstep b A a (c + 1) ha, hval_vstep b A a c ha,
        psum_step (fun c => A ⟨a, ha⟩ c) c hc']
      ring
    have e2 : 2 * A' ⟨a, ha⟩ ⟨c, hc'⟩ =
        -(hval b A' (a + 1) (c + 1) - hval b A' a (c + 1)) +
          (hval b A' (a + 1) c - hval b A' a c) := by
      rw [hval_vstep b A' a (c + 1) ha, hval_vstep b A' a c ha,
        psum_step (fun c => A' ⟨a, ha⟩ c) c hc']
      ring
    have g1 := hv (a + 1) (c + 1) (by omega) (by omega)
    have g2 := hv a (c + 1) (by omega) (by omega)
    have g3 := hv (a + 1) c (by omega) (by omega)
    have g4 := hv a c (by omega) (by omega)
    linarith
  · -- surjective
    rintro h ⟨hh, hbd⟩
    have hcl1 : ∀ i j, i ≤ m → ((cl i j : Pt m n)).1.val = i := by
      intro i j hi
      show min i m = i
      omega
    have hcl2 : ∀ i j, j ≤ n → ((cl i j : Pt m n)).2.val = j := by
      intro i j hj
      show min j n = j
      omega
    have h1 : ∀ i, i ≤ m → ∀ c, c < n → IsSign (h (cl i (c + 1)) - h (cl i c)) := by
      intro i hi c hc'
      refine isSign_iff_abs.mpr (hh _ _ ((grid_adj_iff _ _).mpr ?_))
      rw [hcl1 i (c + 1) hi, hcl1 i c hi, hcl2 i (c + 1) (by omega), hcl2 i c (by omega)]
      omega
    have h2 : ∀ a, a < m → ∀ t, t ≤ n → IsSign (h (cl (a + 1) t) - h (cl a t)) := by
      intro a ha t ht
      refine isSign_iff_abs.mpr (hh _ _ ((grid_adj_iff _ _).mpr ?_))
      rw [hcl1 (a + 1) t (by omega), hcl1 a t (by omega), hcl2 (a + 1) t ht, hcl2 a t ht]
      omega
    have htop : ∀ j, j ≤ n → h (cl 0 j) = -psum b.u j := by
      intro j hj
      have e := hcl1 0 j (Nat.zero_le _)
      rw [hbd _ (Or.inl e), bw_top b _ e, hcl2 0 j hj]
    have hleft : ∀ i, i ≤ m → h (cl i 0) = -psum b.v i := by
      intro i hi
      have e := hcl2 i 0 (Nat.zero_le _)
      rw [hbd _ (Or.inr (Or.inr (Or.inl e))), bw_left b _ e, hcl1 i 0 hi]
    have hbot : ∀ j, j ≤ n → h (cl m j) = -psum b.v m + psum b.u' j := by
      intro j hj
      have e := hcl1 m j le_rfl
      rw [hbd _ (Or.inr (Or.inl e)), bw_bottom hm b _ e, hcl2 m j hj]
    have hright : ∀ i, i ≤ m → h (cl i n) = -psum b.u n + psum b.v' i := by
      intro i hi
      have e := hcl2 i n le_rfl
      rw [hbd _ (Or.inr (Or.inr (Or.inr e))), bw_right hn b hc _ e, hcl1 i n hi]
    have hval_eq : ∀ i j, i ≤ m → j ≤ n →
        hval b (matOf fun i j => h (cl i j)) i j = h (cl i j) :=
      fun i j hi hj => hval_matOf b (fun i j => h (cl i j)) h1 htop hleft i hi j hj
    refine ⟨matOf fun i j => h (cl i j), ?_, ?_⟩
    · rw [mem_gasm_iff_steps b hb]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro a c
        obtain ⟨a, ha⟩ := a
        obtain ⟨c, hc'⟩ := c
        have e : 2 * (matOf (fun i j => h (cl i j)) : Matrix (Fin m) (Fin n) ℤ) ⟨a, ha⟩ ⟨c, hc'⟩ =
            h (cl a (c + 1)) - h (cl a c) - (h (cl (a + 1) (c + 1)) - h (cl (a + 1) c)) :=
          matOf_two (fun i j => h (cl i j)) h1 a c ha hc'
        have s1 := h1 a (by omega) c hc'
        have s2 := h1 (a + 1) (by omega) c hc'
        unfold IsSign at s1 s2
        omega
      · intro i hi c hc'
        rw [hval_eq i (c + 1) hi (by omega), hval_eq i c hi (by omega)]
        exact h1 i hi c hc'
      · intro a ha t ht
        rw [hval_eq (a + 1) t (by omega) ht, hval_eq a t (by omega) ht]
        exact h2 a ha t ht
      · intro c hc'
        rw [hval_eq m (c + 1) le_rfl (by omega), hval_eq m c le_rfl (by omega),
          hbot (c + 1) (by omega), hbot c (by omega), psum_step b.u' c hc']
        ring
      · intro a ha
        rw [hval_eq (a + 1) n (by omega) le_rfl, hval_eq a n (by omega) le_rfl,
          hright (a + 1) (by omega), hright a (by omega), psum_step b.v' a ha]
        ring
    · funext p
      have hp1 := p.1.isLt
      have hp2 := p.2.isLt
      show hval b (matOf fun i j => h (cl i j)) p.1.val p.2.val = h p
      rw [hval_eq _ _ (by omega) (by omega), cl_self]

/-! ### The border walk is a height function on the border -/

theorem psum_parity {k : ℕ} (w : Fin k → ℤ) (hw : ∀ i, IsSign (w i)) :
    ∀ t, t ≤ k → (psum w t - (t : ℤ)) % 2 = 0 := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [psum_zero]
    simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := hw ⟨t, by omega⟩
    rw [psum_step w t (by omega)]
    unfold IsSign at h2
    push_cast
    omega

/-- One step of the border walk along a side is `±1`. -/
theorem bw_step (hm : 1 ≤ m) (hn : 1 ≤ n) (b : Bdry m n) (hb : b.IsSigns) (hc : b.Closed)
    (p q : Pt m n)
    (hstep : (p.1.val = q.1.val ∧ p.2.val + 1 = q.2.val) ∨
      (p.2.val = q.2.val ∧ p.1.val + 1 = q.1.val))
    (hside : (p.1.val = 0 ∧ q.1.val = 0) ∨ (p.1.val = m ∧ q.1.val = m) ∨
      (p.2.val = 0 ∧ q.2.val = 0) ∨ (p.2.val = n ∧ q.2.val = n)) :
    IsSign (borderWalk b p - borderWalk b q) := by
  obtain ⟨hu, hu', hv, hv'⟩ := hb
  have hq1 := q.1.isLt
  have hq2 := q.2.isLt
  rcases hstep with ⟨e, h⟩ | ⟨e, h⟩
  · have hs : (p.1.val = 0 ∧ q.1.val = 0) ∨ (p.1.val = m ∧ q.1.val = m) := by omega
    rcases hs with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [bw_top b p a1, bw_top b q a2, ← h, psum_step b.u p.2.val (by omega)]
      have s := hu ⟨p.2.val, by omega⟩
      unfold IsSign at s ⊢
      omega
    · rw [bw_bottom hm b p a1, bw_bottom hm b q a2, ← h, psum_step b.u' p.2.val (by omega)]
      have s := hu' ⟨p.2.val, by omega⟩
      unfold IsSign at s ⊢
      omega
  · have hs : (p.2.val = 0 ∧ q.2.val = 0) ∨ (p.2.val = n ∧ q.2.val = n) := by omega
    rcases hs with ⟨a1, a2⟩ | ⟨a1, a2⟩
    · rw [bw_left b p a1, bw_left b q a2, ← h, psum_step b.v p.1.val (by omega)]
      have s := hv ⟨p.1.val, by omega⟩
      unfold IsSign at s ⊢
      omega
    · rw [bw_right hn b hc p a1, bw_right hn b hc q a2, ← h, psum_step b.v' p.1.val (by omega)]
      have s := hv' ⟨p.1.val, by omega⟩
      unfold IsSign at s ⊢
      omega

/-- The border walk changes by `±1` along an edge that lies in one side of the border. -/
theorem bw_side (hm : 1 ≤ m) (hn : 1 ≤ n) (b : Bdry m n) (hb : b.IsSigns) (hc : b.Closed)
    (p q : Pt m n) (hadj : (gridGraph m n).Adj p q)
    (hside : (p.1.val = 0 ∧ q.1.val = 0) ∨ (p.1.val = m ∧ q.1.val = m) ∨
      (p.2.val = 0 ∧ q.2.val = 0) ∨ (p.2.val = n ∧ q.2.val = n)) :
    |borderWalk b p - borderWalk b q| = 1 := by
  rcases (grid_adj_iff p q).mp hadj with ⟨e, h | h⟩ | ⟨e, h | h⟩
  · exact isSign_iff_abs.mp (bw_step hm hn b hb hc p q (Or.inl ⟨e, h⟩) hside)
  · rw [abs_sub_comm]
    exact isSign_iff_abs.mp (bw_step hm hn b hb hc q p (Or.inl ⟨e.symm, h⟩) (by omega))
  · exact isSign_iff_abs.mp (bw_step hm hn b hb hc p q (Or.inr ⟨e, h⟩) hside)
  · rw [abs_sub_comm]
    exact isSign_iff_abs.mp (bw_step hm hn b hb hc q p (Or.inr ⟨e.symm, h⟩) (by omega))

/-- The ring profile of a closed boundary is a ring walk. -/
theorem profile_isRingWalk (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (hc : b.Closed) : IsRingWalk m n (profile b) := by
  constructor
  · intro p hp
    have hp1 := p.1.1.isLt
    have hp2 := p.1.2.isLt
    have hpb : p.1.1.val = 0 ∨ p.1.1.val = m ∨ p.1.2.val = 0 ∨ p.1.2.val = n := hp
    have pu := psum_parity b.u hb.1
    have pu' := psum_parity b.u' hb.2.1
    have pv := psum_parity b.v hb.2.2.1
    have pv' := psum_parity b.v' hb.2.2.2
    show (borderWalk b p.1 - ((p.1.1.val : ℤ) + (p.1.2.val : ℤ))) % 2 = 0
    rcases hpb with h | h | h | h
    · rw [bw_top b p.1 h]
      have := pu p.1.2.val (by omega)
      omega
    · rw [bw_bottom (by omega) b p.1 h]
      have := pv m le_rfl
      have := pu' p.1.2.val (by omega)
      omega
    · rw [bw_left b p.1 h]
      have := pv p.1.1.val (by omega)
      omega
    · rw [bw_right (by omega) b hc p.1 h]
      have := pu n le_rfl
      have := pv' p.1.1.val (by omega)
      omega
  · intro p hp q hq hpq
    have hadj : (gridGraph m n).Adj p.1 q.1 := hpq
    have hpb : p.1.1.val = 0 ∨ p.1.1.val = m ∨ p.1.2.val = 0 ∨ p.1.2.val = n := hp
    have hqb : q.1.1.val = 0 ∨ q.1.1.val = m ∨ q.1.2.val = 0 ∨ q.1.2.val = n := hq
    have hpc : ¬((p.1.1.val = 0 ∨ p.1.1.val = m) ∧ (p.1.2.val = 0 ∨ p.1.2.val = n)) := p.2
    have hqc : ¬((q.1.1.val = 0 ∨ q.1.1.val = m) ∧ (q.1.2.val = 0 ∨ q.1.2.val = n)) := q.2
    have ha := (grid_adj_iff p.1 q.1).mp hadj
    exact bw_side (by omega) (by omega) b hb hc p.1 q.1 hadj (by omega)

/-! ### From the grid to `Γ`: the corners play no role -/

open Classical in
/-- Extend a function on `Γ` to the grid by the border walk at the corners. -/
noncomputable def extendCorners (b : Bdry m n) (g : nonCorner m n → ℤ) : Pt m n → ℤ :=
  fun p => if hp : IsCorner m n p then borderWalk b p else g ⟨p, hp⟩

theorem extendCorners_corner (b : Bdry m n) (g : nonCorner m n → ℤ) (p : Pt m n)
    (hp : IsCorner m n p) : extendCorners b g p = borderWalk b p := by
  simp [extendCorners, hp]

theorem extendCorners_nc (b : Bdry m n) (g : nonCorner m n → ℤ) (p : Pt m n)
    (hp : ¬ IsCorner m n p) : extendCorners b g p = g ⟨p, hp⟩ := by
  simp [extendCorners, hp]

/-- Restriction is a bijection from the height functions on `G` with border values `φ` onto
`Ext ρ` (Lemma 2.2). -/
theorem restrict_bijOn (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (hc : b.Closed) :
    Set.BijOn (fun (h : Pt m n → ℤ) (x : nonCorner m n) => h x.1)
      {h | IsHeight (gridGraph m n) h ∧ ∀ p, IsBorder m n p → h p = borderWalk b p}
      (Ext (Γ m n) (ringSet m n) (profile b)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro h ⟨hh, hbd⟩
    exact ⟨fun x y hxy => hh x.1 y.1 hxy, fun x hx => hbd x.1 hx⟩
  · rintro h1 ⟨-, hbd1⟩ h2 ⟨-, hbd2⟩ heq
    funext p
    by_cases hp : IsCorner m n p
    · have hpb : IsBorder m n p := by
        obtain ⟨a, -⟩ := hp
        rcases a with a | a
        · exact Or.inl a
        · exact Or.inr (Or.inl a)
      rw [hbd1 p hpb, hbd2 p hpb]
    · exact congrFun heq ⟨p, hp⟩
  · rintro g ⟨hgH, hgR⟩
    refine ⟨extendCorners b g, ⟨?_, ?_⟩, ?_⟩
    · intro p q hpq
      have ha := (grid_adj_iff p q).mp hpq
      have hp1 := p.1.isLt
      have hp2 := p.2.isLt
      have hq1 := q.1.isLt
      have hq2 := q.2.isLt
      by_cases hp : IsCorner m n p <;> by_cases hq : IsCorner m n q
      · exfalso
        have hp' : (p.1.val = 0 ∨ p.1.val = m) ∧ (p.2.val = 0 ∨ p.2.val = n) := hp
        have hq' : (q.1.val = 0 ∨ q.1.val = m) ∧ (q.2.val = 0 ∨ q.2.val = n) := hq
        omega
      · have hp' : (p.1.val = 0 ∨ p.1.val = m) ∧ (p.2.val = 0 ∨ p.2.val = n) := hp
        have hqb : IsBorder m n q := by
          show q.1.val = 0 ∨ q.1.val = m ∨ q.2.val = 0 ∨ q.2.val = n
          omega
        have e : g ⟨q, hq⟩ = borderWalk b q := hgR ⟨q, hq⟩ hqb
        rw [extendCorners_corner b g p hp, extendCorners_nc b g q hq, e]
        exact bw_side (by omega) (by omega) b hb hc p q hpq (by omega)
      · have hq' : (q.1.val = 0 ∨ q.1.val = m) ∧ (q.2.val = 0 ∨ q.2.val = n) := hq
        have hpb : IsBorder m n p := by
          show p.1.val = 0 ∨ p.1.val = m ∨ p.2.val = 0 ∨ p.2.val = n
          omega
        have e : g ⟨p, hp⟩ = borderWalk b p := hgR ⟨p, hp⟩ hpb
        rw [extendCorners_nc b g p hp, extendCorners_corner b g q hq, e]
        exact bw_side (by omega) (by omega) b hb hc p q hpq (by omega)
      · rw [extendCorners_nc b g p hp, extendCorners_nc b g q hq]
        exact hgH ⟨p, hp⟩ ⟨q, hq⟩ hpq
    · intro p hpb
      by_cases hp : IsCorner m n p
      · exact extendCorners_corner b g p hp
      · rw [extendCorners_nc b g p hp]
        exact hgR ⟨p, hp⟩ hpb
    · funext x
      exact extendCorners_nc b g x.1 x.2

/-- **C2 (Lemma 2.2).** `|𝒜_{m,n}(u,u'|v,v')| = f(ρ)` for a closed boundary. -/
theorem ncard_gasm (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns) (hc : b.Closed) :
    (gasm b).ncard = numExt (Γ m n) (ringSet m n) (profile b) := by
  have h1 := heightOf_bijOn (by omega) (by omega) b hb hc
  have h2 := restrict_bijOn hm hn b hb hc
  unfold numExt
  rw [← h2.image_eq, h2.injOn.ncard_image, ← h1.image_eq, h1.injOn.ncard_image]

/-! ### Flat profiles and the family `ℬ` -/

/-- `1` on even numbers and `0` on odd numbers. -/
def ev (k : ℕ) : ℤ := if k % 2 = 0 then 1 else 0

theorem ev_eq_of {a b : ℕ} (h : (a + b) % 2 = 0) : ev a = ev b := by
  unfold ev
  split_ifs <;> omega

theorem ev_ne_of {a b : ℕ} (h : (a + b) % 2 = 1) : ev a = 1 - ev b := by
  unfold ev
  split_ifs <;> omega

theorem ev_cases (k : ℕ) : ev k = 0 ∨ ev k = 1 := by
  unfold ev
  split_ifs <;> simp

theorem neg_one_pow_ev (k : ℕ) : (-1 : ℤ) ^ k = 2 * ev k - 1 := by
  unfold ev
  rcases Nat.even_or_odd k with h | h
  · have e := Nat.even_iff.mp h
    rw [h.neg_one_pow]
    simp [e]
  · have e := Nat.odd_iff.mp h
    rw [h.neg_one_pow]
    simp [e]

/-- A walk whose steps follow the checkerboard pattern takes two values, by parity. -/
theorem walk_values (W : ℕ → ℤ) (c δ : ℤ) (s N : ℕ) (h1 : W 1 = c - δ * ev (s + 1))
    (hstep : ∀ j, 1 ≤ j → j + 1 < N → W (j + 1) - W j = -δ * (-1) ^ (s + j + 1)) :
    ∀ j, 1 ≤ j → j < N → W j = c - δ * ev (s + j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    exact h1
  | succ j hj ih =>
    intro hlt
    have h2 := ih (by omega)
    have h3 := hstep j hj hlt
    rw [neg_one_pow_ev] at h3
    have e : ev (s + (j + 1)) = 1 - ev (s + j) := ev_ne_of (by omega)
    have e' : ev (s + j + 1) = 1 - ev (s + j) := ev_ne_of (by omega)
    rw [e]
    rw [e'] at h3
    linarith

/-- The four sides of the border walk of a boundary in `ℬ` (proof of Lemma 2.4, converse part):
each side takes the value `c` on odd and `c - δ` on even vertices, and the boundary is closed. -/
theorem family_values (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : InFamily b) :
    ∃ c δ : ℤ, IsSign δ ∧
      (∀ j, 1 ≤ j → j < n → -psum b.u j = c - δ * ev (0 + j)) ∧
      (∀ i, 1 ≤ i → i < m → -psum b.v i = c - δ * ev (0 + i)) ∧
      (∀ j, 1 ≤ j → j < n → -psum b.v m + psum b.u' j = c - δ * ev (m + j)) ∧
      (∀ i, 1 ≤ i → i < m → -psum b.u n + psum b.v' i = c - δ * ev (n + i)) ∧
      b.Closed := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, δ, hδ, hu, hv, c1, c2, c3, c4⟩ := hb
  have ev1 : ∀ s : ℕ, s % 2 = 0 → ev (s + 1) = 0 := by
    intro s hs
    unfold ev
    split_ifs <;> omega
  -- top side
  have hT := walk_values (fun j => -psum b.u j) (-b.u ⟨0, by omega⟩) δ 0 (n' + 1)
    (by
      show -psum b.u 1 = _
      rw [psum_step b.u 0 (by omega), psum_zero, ev1 0 rfl]
      ring)
    (by
      intro j h1 h2
      show -psum b.u (j + 1) - -psum b.u j = _
      have e := (hu ⟨j, by omega⟩ h1 (by show j + 2 ≤ n' + 1; omega)).1
      rw [psum_step b.u j (by omega), e, Nat.zero_add]
      ring)
  -- left side
  have hL := walk_values (fun i => -psum b.v i) (-b.u ⟨0, by omega⟩) δ 0 (m' + 1)
    (by
      show -psum b.v 1 = _
      have e := c1 ⟨0, by omega⟩ ⟨0, by omega⟩ rfl rfl
      rw [psum_step b.v 0 (by omega), psum_zero, ev1 0 rfl, e]
      ring)
    (by
      intro i h1 h2
      show -psum b.v (i + 1) - -psum b.v i = _
      have e := (hv ⟨i, by omega⟩ h1 (by show i + 2 ≤ m' + 1; omega)).1
      rw [psum_step b.v i (by omega), e, Nat.zero_add]
      ring)
  -- bottom side
  have hB := walk_values (fun j => -psum b.v (m' + 1) + psum b.u' j) (-b.u ⟨0, by omega⟩) δ
    (m' + 1) (n' + 1)
    (by
      show -psum b.v (m' + 1) + psum b.u' 1 = _
      have e := c3 ⟨0, by omega⟩ ⟨m', by omega⟩ rfl rfl
      have e2 := hL m' (by omega) (by omega)
      have e3 : ev (m' + 1 + 1) = ev (0 + m') := ev_eq_of (by omega)
      rw [psum_step b.u' 0 (by omega), psum_zero, psum_step b.v m' (by omega), e, e3]
      linarith)
    (by
      intro j h1 h2
      show -psum b.v (m' + 1) + psum b.u' (j + 1) - (-psum b.v (m' + 1) + psum b.u' j) = _
      have e := (hu ⟨j, by omega⟩ h1 (by show j + 2 ≤ n' + 1; omega)).2
      have e3 : ev (j + 1 + (m' + 1) + 1) = 1 - ev (m' + 1 + j + 1) := ev_ne_of (by omega)
      rw [psum_step b.u' j (by omega), e, neg_one_pow_ev, neg_one_pow_ev, e3]
      ring)
  -- right side
  have hR := walk_values (fun i => -psum b.u (n' + 1) + psum b.v' i) (-b.u ⟨0, by omega⟩) δ
    (n' + 1) (m' + 1)
    (by
      show -psum b.u (n' + 1) + psum b.v' 1 = _
      have e := c2 ⟨n', by omega⟩ ⟨0, by omega⟩ rfl rfl
      have e2 := hT n' (by omega) (by omega)
      have e3 : ev (n' + 1 + 1) = ev (0 + n') := ev_eq_of (by omega)
      rw [psum_step b.v' 0 (by omega), psum_zero, psum_step b.u n' (by omega), e, e3]
      linarith)
    (by
      intro i h1 h2
      show -psum b.u (n' + 1) + psum b.v' (i + 1) - (-psum b.u (n' + 1) + psum b.v' i) = _
      have e := (hv ⟨i, by omega⟩ h1 (by show i + 2 ≤ m' + 1; omega)).2
      have e3 : ev (i + 1 + (n' + 1) + 1) = 1 - ev (n' + 1 + i + 1) := ev_ne_of (by omega)
      rw [psum_step b.v' i (by omega), e, neg_one_pow_ev, neg_one_pow_ev, e3]
      ring)
  refine ⟨-b.u ⟨0, by omega⟩, δ, hδ, hT, hL, hB, hR, ?_⟩
  have e := c4 ⟨n', by omega⟩ ⟨m', by omega⟩ rfl rfl
  have e1 := hB n' (by omega) (by omega)
  have e2 := hR m' (by omega) (by omega)
  have e3 : ev (m' + 1 + n') = ev (n' + 1 + m') := ev_eq_of (by omega)
  unfold Bdry.Closed
  rw [psum_step b.u' n' (by omega), psum_step b.v' m' (by omega), e]
  rw [e3] at e1
  linarith

/-- **C3 (Lemma 2.4).** Every boundary in `ℬ_{m,n}` is closed. -/
theorem closed_of_inFamily (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : InFamily b) :
    b.Closed := by
  obtain ⟨c, δ, -, -, -, -, -, hc⟩ := family_values hm hn b hb
  exact hc

/-- Lemma 2.4, converse part: a boundary in `ℬ` has a flat ring profile. -/
theorem isFlat_of_inFamily (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : InFamily b) :
    IsFlat m n (profile b) := by
  obtain ⟨c, δ, hδ, hT, hL, hB, hR, hc⟩ := family_values hm hn b hb
  have key : ∀ p ∈ ringSet m n, ∃ t, profile b p = c - δ * ev t := by
    intro p hp
    have hp1 := p.1.1.isLt
    have hp2 := p.1.2.isLt
    have hpb : p.1.1.val = 0 ∨ p.1.1.val = m ∨ p.1.2.val = 0 ∨ p.1.2.val = n := hp
    have hpc : ¬((p.1.1.val = 0 ∨ p.1.1.val = m) ∧ (p.1.2.val = 0 ∨ p.1.2.val = n)) := p.2
    show ∃ t, borderWalk b p.1 = _
    rcases hpb with h | h | h | h
    · exact ⟨0 + p.1.2.val, by
        rw [bw_top b p.1 h]
        exact hT _ (by omega) (by omega)⟩
    · exact ⟨m + p.1.2.val, by
        rw [bw_bottom (by omega) b p.1 h]
        exact hB _ (by omega) (by omega)⟩
    · exact ⟨0 + p.1.1.val, by
        rw [bw_left b p.1 h]
        exact hL _ (by omega) (by omega)⟩
    · exact ⟨n + p.1.1.val, by
        rw [bw_right (by omega) b hc p.1 h]
        exact hR _ (by omega) (by omega)⟩
  intro p hp q hq
  obtain ⟨t, ht⟩ := key p hp
  obtain ⟨t', ht'⟩ := key q hq
  rw [ht, ht', abs_le]
  unfold IsSign at hδ
  rcases ev_cases t with e | e <;> rcases ev_cases t' with e' | e' <;>
    rcases hδ with rfl | rfl <;> rw [e, e'] <;> constructor <;> norm_num

/-- The grid vertex `(i,j)`. -/
def gp {m n : ℕ} (i j : ℕ) (hi : i ≤ m) (hj : j ≤ n) : Pt m n :=
  (⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩)

theorem bwT (b : Bdry m n) (j : ℕ) (hj : j ≤ n) :
    borderWalk b (gp 0 j (Nat.zero_le m) hj) = -psum b.u j :=
  bw_top b _ rfl

theorem bwL (b : Bdry m n) (i : ℕ) (hi : i ≤ m) :
    borderWalk b (gp i 0 hi (Nat.zero_le n)) = -psum b.v i :=
  bw_left b _ rfl

theorem bwB (hm : 1 ≤ m) (b : Bdry m n) (j : ℕ) (hj : j ≤ n) :
    borderWalk b (gp m j le_rfl hj) = -psum b.v m + psum b.u' j :=
  bw_bottom hm b _ rfl

theorem bwR (hn : 1 ≤ n) (b : Bdry m n) (hc : b.Closed) (i : ℕ) (hi : i ≤ m) :
    borderWalk b (gp i n hi le_rfl) = -psum b.u n + psum b.v' i :=
  bw_right hn b hc _ rfl

/-- Lemma 2.4, direct part: a closed boundary with a flat ring profile is in `ℬ`. -/
theorem inFamily_of_isFlat (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (hc : b.Closed) (hflat : IsFlat m n (profile b)) : InFamily b := by
  have hρ := profile_isRingWalk hm hn b hb hc
  have hfact : ∀ x ∈ ringSet m n, ∀ y ∈ ringSet m n,
      (profile b x - ((x.1.1.val : ℤ) + (x.1.2.val : ℤ))) % 2 = 0 ∧
      (profile b y - ((y.1.1.val : ℤ) + (y.1.2.val : ℤ))) % 2 = 0 ∧
      -1 ≤ profile b x - profile b y ∧ profile b x - profile b y ≤ 1 := by
    intro x hx y hy
    have h := abs_le.mp (hflat x hx y hy)
    exact ⟨hρ.1 x hx, hρ.1 y hy, h.1, h.2⟩
  have hδ : ∃ δ : ℤ, IsSign δ ∧ ∀ x ∈ ringSet m n, ∀ y ∈ ringSet m n,
      profile b x - profile b y =
        δ * (ev (y.1.1.val + y.1.2.val) - ev (x.1.1.val + x.1.2.val)) := by
    by_cases hE : ∃ q0 ∈ ringSet m n, (q0.1.1.val + q0.1.2.val) % 2 = 0
    · obtain ⟨q0, hq0, he0⟩ := hE
      have hp0 : (pt 0 1 (by omega) (by omega) (by omega) : nonCorner m n) ∈ ringSet m n := by
        show (0 = 0 ∨ 0 = m ∨ 1 = 0 ∨ 1 = n)
        omega
      generalize hP : (pt 0 1 (by omega) (by omega) (by omega) : nonCorner m n) = p0 at hp0
      have hpar0 : (p0.1.1.val + p0.1.2.val) % 2 = 1 := by
        rw [← hP]
        rfl
      refine ⟨profile b p0 - profile b q0, ?_, ?_⟩
      · have f := hfact p0 hp0 q0 hq0
        unfold IsSign
        omega
      · intro x hx y hy
        have f1 := hfact x hx y hy
        have f2 := hfact x hx p0 hp0
        have f3 := hfact x hx q0 hq0
        have f4 := hfact y hy p0 hp0
        have f5 := hfact y hy q0 hq0
        have f6 := hfact p0 hp0 q0 hq0
        by_cases ex : (x.1.1.val + x.1.2.val) % 2 = 0 <;>
          by_cases ey : (y.1.1.val + y.1.2.val) % 2 = 0
        · have evx : ev (x.1.1.val + x.1.2.val) = 1 := by simp [ev, ex]
          have evy : ev (y.1.1.val + y.1.2.val) = 1 := by simp [ev, ey]
          have key : profile b x - profile b y = 0 := by omega
          rw [evx, evy, key]
          ring
        · have evx : ev (x.1.1.val + x.1.2.val) = 1 := by simp [ev, ex]
          have evy : ev (y.1.1.val + y.1.2.val) = 0 := by simp [ev, ey]
          have key : profile b x - profile b y = -(profile b p0 - profile b q0) := by omega
          rw [evx, evy, key]
          ring
        · have evx : ev (x.1.1.val + x.1.2.val) = 0 := by simp [ev, ex]
          have evy : ev (y.1.1.val + y.1.2.val) = 1 := by simp [ev, ey]
          have key : profile b x - profile b y = profile b p0 - profile b q0 := by omega
          rw [evx, evy, key]
          ring
        · have evx : ev (x.1.1.val + x.1.2.val) = 0 := by simp [ev, ex]
          have evy : ev (y.1.1.val + y.1.2.val) = 0 := by simp [ev, ey]
          have key : profile b x - profile b y = 0 := by omega
          rw [evx, evy, key]
          ring
    · push Not at hE
      refine ⟨1, Or.inl rfl, ?_⟩
      intro x hx y hy
      have f1 := hfact x hx y hy
      have ex := hE x hx
      have ey := hE y hy
      have evx : ev (x.1.1.val + x.1.2.val) = 0 := by simp [ev, ex]
      have evy : ev (y.1.1.val + y.1.2.val) = 0 := by simp [ev, ey]
      have key : profile b x - profile b y = 0 := by omega
      rw [evx, evy, key]
      ring
  obtain ⟨δ, hδs, R⟩ := hδ
  -- the same relation in coordinates
  have Rc : ∀ (i j i' j' : ℕ) (hi : i ≤ m) (hj : j ≤ n) (hi' : i' ≤ m) (hj' : j' ≤ n),
      ¬((i = 0 ∨ i = m) ∧ (j = 0 ∨ j = n)) → ¬((i' = 0 ∨ i' = m) ∧ (j' = 0 ∨ j' = n)) →
      (i = 0 ∨ i = m ∨ j = 0 ∨ j = n) → (i' = 0 ∨ i' = m ∨ j' = 0 ∨ j' = n) →
      borderWalk b (gp i j hi hj) - borderWalk b (gp i' j' hi' hj') =
        δ * (ev (i' + j') - ev (i + j)) :=
    fun i j i' j' hi hj hi' hj' hnc hnc' hr hr' =>
      R (pt i j hi hj hnc) hr (pt i' j' hi' hj' hnc') hr'
  refine ⟨hb, δ, hδs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, hj⟩ h1 h2
    have h1' : 1 ≤ j := h1
    have h2' : j + 2 ≤ n := h2
    constructor
    · have r := Rc 0 j 0 (j + 1) (Nat.zero_le m) (by omega) (Nat.zero_le m) (by omega)
        (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
      rw [bwT b j (by omega), bwT b (j + 1) (by omega), psum_step b.u j hj] at r
      have e1 : ev (0 + (j + 1)) = ev (j + 1) := ev_eq_of (by omega)
      have e2 : ev (0 + j) = 1 - ev (j + 1) := ev_ne_of (by omega)
      rw [e1, e2] at r
      rw [neg_one_pow_ev]
      linarith
    · have r := Rc m (j + 1) m j le_rfl (by omega) le_rfl (by omega)
        (by omega) (by omega) (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
      rw [bwB (by omega) b (j + 1) (by omega), bwB (by omega) b j (by omega),
        psum_step b.u' j hj] at r
      have e1 : ev (m + j) = ev (j + 1 + m + 1) := ev_eq_of (by omega)
      have e2 : ev (m + (j + 1)) = 1 - ev (j + 1 + m + 1) := ev_ne_of (by omega)
      rw [e1, e2] at r
      rw [neg_one_pow_ev]
      linarith
  · rintro ⟨i, hi⟩ h1 h2
    have h1' : 1 ≤ i := h1
    have h2' : i + 2 ≤ m := h2
    constructor
    · have r := Rc i 0 (i + 1) 0 (by omega) (Nat.zero_le n) (by omega) (Nat.zero_le n)
        (by omega) (by omega) (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inl rfl)))
      rw [bwL b i (by omega), bwL b (i + 1) (by omega), psum_step b.v i hi] at r
      have e1 : ev (i + 1 + 0) = ev (i + 1) := ev_eq_of (by omega)
      have e2 : ev (i + 0) = 1 - ev (i + 1) := ev_ne_of (by omega)
      rw [e1, e2] at r
      rw [neg_one_pow_ev]
      linarith
    · have r := Rc (i + 1) n i n (by omega) le_rfl (by omega) le_rfl
        (by omega) (by omega) (Or.inr (Or.inr (Or.inr rfl))) (Or.inr (Or.inr (Or.inr rfl)))
      rw [bwR (by omega) b hc (i + 1) (by omega), bwR (by omega) b hc i (by omega),
        psum_step b.v' i hi] at r
      have e1 : ev (i + n) = ev (i + 1 + n + 1) := ev_eq_of (by omega)
      have e2 : ev (i + 1 + n) = 1 - ev (i + 1 + n + 1) := ev_ne_of (by omega)
      rw [e1, e2] at r
      rw [neg_one_pow_ev]
      linarith
  · rintro ⟨j, hj⟩ ⟨i, hi⟩ h1 h2
    have h1' : j = 0 := h1
    have h2' : i = 0 := h2
    subst h1' h2'
    have r := Rc 0 1 1 0 (Nat.zero_le m) (by omega) (by omega) (Nat.zero_le n)
      (by omega) (by omega) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    rw [bwT b 1 (by omega), bwL b 1 (by omega), psum_step b.u 0 hj, psum_step b.v 0 hi,
      psum_zero, psum_zero] at r
    have e1 : ev (1 + 0) = ev (0 + 1) := ev_eq_of (by omega)
    rw [e1] at r
    linarith
  · rintro ⟨j, hj⟩ ⟨i, hi⟩ h1 h2
    have h1' : j + 1 = n := h1
    have h2' : i = 0 := h2
    subst h1' h2'
    have r := Rc 0 j 1 (j + 1) (Nat.zero_le m) (by omega) (by omega) le_rfl
      (by omega) (by omega) (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl)))
    rw [bwT b j (by omega), bwR (by omega) b hc 1 (by omega), psum_step b.u j hj,
      psum_step b.v' 0 hi, psum_zero] at r
    have e1 : ev (1 + (j + 1)) = ev (0 + j) := ev_eq_of (by omega)
    rw [e1] at r
    linarith
  · rintro ⟨j, hj⟩ ⟨i, hi⟩ h1 h2
    have h1' : j = 0 := h1
    have h2' : i + 1 = m := h2
    subst h1' h2'
    have r := Rc (i + 1) 1 i 0 le_rfl (by omega) (by omega) (Nat.zero_le n)
      (by omega) (by omega) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
    rw [bwB (by omega) b 1 (by omega), bwL b i (by omega), psum_step b.v i hi,
      psum_step b.u' 0 hj, psum_zero] at r
    have e1 : ev (i + 0) = ev (i + 1 + 1) := ev_eq_of (by omega)
    rw [e1] at r
    linarith
  · rintro ⟨j, hj⟩ ⟨i, hi⟩ h1 h2
    have h1' : j + 1 = n := h1
    have h2' : i + 1 = m := h2
    subst h1' h2'
    have r := Rc (i + 1) j i (j + 1) le_rfl (by omega) (by omega) le_rfl
      (by omega) (by omega) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inr rfl)))
    rw [bwB (by omega) b j (by omega), bwR (by omega) b hc i (by omega)] at r
    have hc' : -psum b.v (i + 1) + psum b.u' (j + 1) = -psum b.u (j + 1) + psum b.v' (i + 1) :=
      hc
    rw [psum_step b.u' j hj, psum_step b.v' i hi] at hc'
    have e1 : ev (i + (j + 1)) = ev (i + 1 + j) := ev_eq_of (by omega)
    rw [e1] at r
    linarith

/-- **C3 (Lemma 2.4).** A closed boundary has a flat ring profile iff it is in `ℬ_{m,n}`. -/
theorem isFlat_profile_iff (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns)
    (hc : b.Closed) : IsFlat m n (profile b) ↔ InFamily b :=
  ⟨inFamily_of_isFlat hm hn b hb hc, isFlat_of_inFamily hm hn b⟩

/-! ### Counting the family `ℬ` -/

/-- The boundary `B_{m,n}(δ, ε)` of Definition 1.2, for `t = (δ, ε₁, ε₂, ε₃, ε₄)`. -/
def build (t : ℤ × ℤ × ℤ × ℤ × ℤ) : Bdry m n where
  u := fun j => if j.val = 0 then t.2.1 else if j.val + 1 = n then t.2.2.1
    else t.1 * (-1) ^ (j.val + 1)
  u' := fun j => if j.val = 0 then t.2.2.2.1 else if j.val + 1 = n then t.2.2.2.2
    else t.1 * (-1) ^ (j.val + 1 + m + 1)
  v := fun i => if i.val = 0 then t.2.1 else if i.val + 1 = m then t.2.2.2.1
    else t.1 * (-1) ^ (i.val + 1)
  v' := fun i => if i.val = 0 then t.2.2.1 else if i.val + 1 = m then t.2.2.2.2
    else t.1 * (-1) ^ (i.val + 1 + n + 1)

theorem isSign_mul_pow {δ : ℤ} (h : IsSign δ) (k : ℕ) : IsSign (δ * (-1) ^ k) := by
  rw [neg_one_pow_ev]
  unfold IsSign at *
  rcases ev_cases k with e | e <;> rcases h with rfl | rfl <;> rw [e] <;> norm_num

/-- The parameters `(δ, ε₁, ε₂, ε₃, ε₄) ∈ {±1}⁵`. -/
def signTuples : Set (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  {t | IsSign t.1 ∧ IsSign t.2.1 ∧ IsSign t.2.2.1 ∧ IsSign t.2.2.2.1 ∧ IsSign t.2.2.2.2}

theorem build_inFamily (hm : 2 ≤ m) (hn : 2 ≤ n) (t : ℤ × ℤ × ℤ × ℤ × ℤ)
    (ht : t ∈ signTuples) : InFamily (build t : Bdry m n) := by
  obtain ⟨δ, e1, e2, e3, e4⟩ := t
  obtain ⟨hδ, h1, h2, h3, h4⟩ := ht
  have hδ' : IsSign δ := hδ
  have h1' : IsSign e1 := h1
  have h2' : IsSign e2 := h2
  have h3' : IsSign e3 := h3
  have h4' : IsSign e4 := h4
  refine ⟨⟨?_, ?_, ?_, ?_⟩, δ, hδ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show IsSign (if j.val = 0 then e1 else if j.val + 1 = n then e2 else δ * (-1) ^ (j.val + 1))
    split_ifs
    exacts [h1', h2', isSign_mul_pow hδ' _]
  · intro j
    show IsSign (if j.val = 0 then e3 else if j.val + 1 = n then e4
      else δ * (-1) ^ (j.val + 1 + m + 1))
    split_ifs
    exacts [h3', h4', isSign_mul_pow hδ' _]
  · intro i
    show IsSign (if i.val = 0 then e1 else if i.val + 1 = m then e3 else δ * (-1) ^ (i.val + 1))
    split_ifs
    exacts [h1', h3', isSign_mul_pow hδ' _]
  · intro i
    show IsSign (if i.val = 0 then e2 else if i.val + 1 = m then e4
      else δ * (-1) ^ (i.val + 1 + n + 1))
    split_ifs
    exacts [h2', h4', isSign_mul_pow hδ' _]
  · intro j hj1 hj2
    constructor
    · show (if j.val = 0 then e1 else if j.val + 1 = n then e2 else δ * (-1) ^ (j.val + 1)) = _
      split_ifs <;> first | rfl | (exfalso; omega)
    · show (if j.val = 0 then e3 else if j.val + 1 = n then e4
        else δ * (-1) ^ (j.val + 1 + m + 1)) = _
      split_ifs <;> first | rfl | (exfalso; omega)
  · intro i hi1 hi2
    constructor
    · show (if i.val = 0 then e1 else if i.val + 1 = m then e3 else δ * (-1) ^ (i.val + 1)) = _
      split_ifs <;> first | rfl | (exfalso; omega)
    · show (if i.val = 0 then e2 else if i.val + 1 = m then e4
        else δ * (-1) ^ (i.val + 1 + n + 1)) = _
      split_ifs <;> first | rfl | (exfalso; omega)
  · intro j i hj hi
    show (if j.val = 0 then e1 else if j.val + 1 = n then e2 else δ * (-1) ^ (j.val + 1)) =
      (if i.val = 0 then e1 else if i.val + 1 = m then e3 else δ * (-1) ^ (i.val + 1))
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro j i hj hi
    show (if j.val = 0 then e1 else if j.val + 1 = n then e2 else δ * (-1) ^ (j.val + 1)) =
      (if i.val = 0 then e2 else if i.val + 1 = m then e4 else δ * (-1) ^ (i.val + 1 + n + 1))
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro j i hj hi
    show (if j.val = 0 then e3 else if j.val + 1 = n then e4
        else δ * (-1) ^ (j.val + 1 + m + 1)) =
      (if i.val = 0 then e1 else if i.val + 1 = m then e3 else δ * (-1) ^ (i.val + 1))
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro j i hj hi
    show (if j.val = 0 then e3 else if j.val + 1 = n then e4
        else δ * (-1) ^ (j.val + 1 + m + 1)) =
      (if i.val = 0 then e2 else if i.val + 1 = m then e4 else δ * (-1) ^ (i.val + 1 + n + 1))
    split_ifs <;> first | rfl | (exfalso; omega)

/-- A boundary that satisfies the conditions of Definition 1.2 for `δ` is `B(δ, ε)` with `ε` read
off from the ends of `u` and `u'`. -/
theorem build_eq (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (δ : ℤ)
    (hu : ∀ j : Fin n, 1 ≤ j.val → j.val + 2 ≤ n →
      b.u j = δ * (-1) ^ (j.val + 1) ∧ b.u' j = δ * (-1) ^ (j.val + 1 + m + 1))
    (hv : ∀ i : Fin m, 1 ≤ i.val → i.val + 2 ≤ m →
      b.v i = δ * (-1) ^ (i.val + 1) ∧ b.v' i = δ * (-1) ^ (i.val + 1 + n + 1))
    (c1 : ∀ (j : Fin n) (i : Fin m), j.val = 0 → i.val = 0 → b.u j = b.v i)
    (c2 : ∀ (j : Fin n) (i : Fin m), j.val + 1 = n → i.val = 0 → b.u j = b.v' i)
    (c3 : ∀ (j : Fin n) (i : Fin m), j.val = 0 → i.val + 1 = m → b.u' j = b.v i)
    (c4 : ∀ (j : Fin n) (i : Fin m), j.val + 1 = n → i.val + 1 = m → b.u' j = b.v' i) :
    build (δ, b.u ⟨0, by omega⟩, b.u ⟨n - 1, by omega⟩, b.u' ⟨0, by omega⟩,
      b.u' ⟨n - 1, by omega⟩) = b := by
  have hn1 : n - 1 + 1 = n := by omega
  ext j
  · show (if j.val = 0 then b.u ⟨0, _⟩ else if j.val + 1 = n then b.u ⟨n - 1, _⟩
      else δ * (-1) ^ (j.val + 1)) = b.u j
    split_ifs with a1 a2
    · congr 1
      exact Fin.ext a1.symm
    · congr 1
      apply Fin.ext
      show n - 1 = j.val
      omega
    · exact ((hu j (by omega) (by omega)).1).symm
  · show (if j.val = 0 then b.u' ⟨0, _⟩ else if j.val + 1 = n then b.u' ⟨n - 1, _⟩
      else δ * (-1) ^ (j.val + 1 + m + 1)) = b.u' j
    split_ifs with a1 a2
    · congr 1
      exact Fin.ext a1.symm
    · congr 1
      apply Fin.ext
      show n - 1 = j.val
      omega
    · exact ((hu j (by omega) (by omega)).2).symm
  · show (if j.val = 0 then b.u ⟨0, _⟩ else if j.val + 1 = m then b.u' ⟨0, _⟩
      else δ * (-1) ^ (j.val + 1)) = b.v j
    split_ifs with a1 a2
    · exact c1 _ j rfl a1
    · exact c3 _ j rfl a2
    · exact ((hv j (by omega) (by omega)).1).symm
  · show (if j.val = 0 then b.u ⟨n - 1, _⟩ else if j.val + 1 = m then b.u' ⟨n - 1, _⟩
      else δ * (-1) ^ (j.val + 1 + n + 1)) = b.v' j
    split_ifs with a1 a2
    · exact c2 _ j hn1 a1
    · exact c4 _ j hn1 a2
    · exact ((hv j (by omega) (by omega)).2).symm

/-- `ε` is determined by the boundary. -/
theorem build_eps_inj (hn : 2 ≤ n) (t t' : ℤ × ℤ × ℤ × ℤ × ℤ)
    (h : (build t : Bdry m n) = build t') : t.2 = t'.2 := by
  obtain ⟨δ, e1, e2, e3, e4⟩ := t
  obtain ⟨δ', e1', e2', e3', e4'⟩ := t'
  have hne : ¬ (n - 1 = 0) := by omega
  have hn1 : n - 1 + 1 = n := by omega
  have a1 : (build (δ, e1, e2, e3, e4) : Bdry m n).u ⟨0, by omega⟩ =
      (build (δ', e1', e2', e3', e4') : Bdry m n).u ⟨0, by omega⟩ := by rw [h]
  have a2 : (build (δ, e1, e2, e3, e4) : Bdry m n).u ⟨n - 1, by omega⟩ =
      (build (δ', e1', e2', e3', e4') : Bdry m n).u ⟨n - 1, by omega⟩ := by rw [h]
  have a3 : (build (δ, e1, e2, e3, e4) : Bdry m n).u' ⟨0, by omega⟩ =
      (build (δ', e1', e2', e3', e4') : Bdry m n).u' ⟨0, by omega⟩ := by rw [h]
  have a4 : (build (δ, e1, e2, e3, e4) : Bdry m n).u' ⟨n - 1, by omega⟩ =
      (build (δ', e1', e2', e3', e4') : Bdry m n).u' ⟨n - 1, by omega⟩ := by rw [h]
  simp only [build, ↓reduceIte] at a1 a3
  simp only [build, hne, hn1, ↓reduceIte] at a2 a4
  show (e1, e2, e3, e4) = (e1', e2', e3', e4')
  rw [a1, a2, a3, a4]

/-- `δ` is determined by the boundary if some vector has an interior entry. -/
theorem build_delta_inj (hm : 2 ≤ m) (hn : 2 ≤ n) (h3 : 3 ≤ m ∨ 3 ≤ n)
    (t t' : ℤ × ℤ × ℤ × ℤ × ℤ) (h : (build t : Bdry m n) = build t') : t.1 = t'.1 := by
  rcases h3 with h3 | h3
  · have a : (build t : Bdry m n).v ⟨1, by omega⟩ = (build t' : Bdry m n).v ⟨1, by omega⟩ := by
      rw [h]
    have h1 : ¬ (1 + 1 = m) := by omega
    simp [build, h1] at a
    exact a
  · have a : (build t : Bdry m n).u ⟨1, by omega⟩ = (build t' : Bdry m n).u ⟨1, by omega⟩ := by
      rw [h]
    have h1 : ¬ (1 + 1 = n) := by omega
    simp [build, h1] at a
    exact a

theorem signTuples_ncard : signTuples.ncard = 32 := by
  have h : signTuples = ↑((({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ) ×ˢ
      ({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ))) := by
    ext ⟨a, b, c, d, e⟩
    simp [signTuples, IsSign]
  rw [h, Set.ncard_coe_finset]
  rfl

/-- **C3.** `|ℬ_{m,n}| = 32` if `m ≥ 3` or `n ≥ 3`. -/
theorem ncard_family (hm : 2 ≤ m) (hn : 2 ≤ n) (h3 : 3 ≤ m ∨ 3 ≤ n) :
    {b : Bdry m n | InFamily b}.ncard = 32 := by
  have himg : {b : Bdry m n | InFamily b} = build '' signTuples := by
    ext b
    constructor
    · rintro ⟨hs, δ, hδ, hu, hv, c1, c2, c3, c4⟩
      exact ⟨_, ⟨hδ, hs.1 _, hs.1 _, hs.2.1 _, hs.2.1 _⟩, build_eq hm hn b δ hu hv c1 c2 c3 c4⟩
    · rintro ⟨t, ht, rfl⟩
      exact build_inFamily hm hn t ht
  have hinj : Set.InjOn (build : ℤ × ℤ × ℤ × ℤ × ℤ → Bdry m n) signTuples := by
    intro t _ t' _ h
    exact Prod.ext (build_delta_inj hm hn h3 t t' h) (build_eps_inj hn t t' h)
  rw [himg, hinj.ncard_image, signTuples_ncard]

/-- **C3.** `|ℬ_{2,2}| = 16`. -/
theorem ncard_family_two : {b : Bdry 2 2 | InFamily b}.ncard = 16 := by
  have himg : {b : Bdry 2 2 | InFamily b} = build '' {t | t.1 = 1 ∧ t ∈ signTuples} := by
    ext b
    constructor
    · rintro ⟨hs, δ, hδ, hu, hv, c1, c2, c3, c4⟩
      refine ⟨_, ⟨rfl, Or.inl rfl, hs.1 _, hs.1 _, hs.2.1 _, hs.2.1 _⟩,
        build_eq le_rfl le_rfl b 1 ?_ ?_ c1 c2 c3 c4⟩
      · intro j h1 h2
        exfalso
        omega
      · intro i h1 h2
        exfalso
        omega
    · rintro ⟨t, ⟨-, ht⟩, rfl⟩
      exact build_inFamily le_rfl le_rfl t ht
  have hinj : Set.InjOn (build : ℤ × ℤ × ℤ × ℤ × ℤ → Bdry 2 2) {t | t.1 = 1 ∧ t ∈ signTuples} := by
    rintro t ⟨h1, -⟩ t' ⟨h1', -⟩ h
    exact Prod.ext (h1.trans h1'.symm) (build_eps_inj le_rfl t t' h)
  have hcard : ({t : ℤ × ℤ × ℤ × ℤ × ℤ | t.1 = 1 ∧ t ∈ signTuples}).ncard = 16 := by
    have h : {t : ℤ × ℤ × ℤ × ℤ × ℤ | t.1 = 1 ∧ t ∈ signTuples} =
        ↑((({1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ) ×ˢ
          ({1, -1} : Finset ℤ) ×ˢ ({1, -1} : Finset ℤ))) := by
      ext ⟨a, b, c, d, e⟩
      simp [signTuples, IsSign]
      omega
    rw [h, Set.ncard_coe_finset]
    rfl
  rw [himg, hinj.ncard_image, hcard]

/-- **C4 (Theorem 1.3), inequality.** -/
theorem ncard_gasm_le (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns) :
    (gasm b).ncard ≤ N m n := by
  by_cases hc : b.Closed
  · rw [ncard_gasm hm hn b hb hc]
    exact numExt_le_N m n hm hn _ (profile_isRingWalk hm hn b hb hc)
  · rw [gasm_eq_empty_of_not_closed (by omega) (by omega) b hb hc, Set.ncard_empty]
    exact Nat.zero_le _

/-- **C4 (Theorem 1.3), equality case.** The class has the maximum size `N(m,n)` if and only if
the boundary belongs to `ℬ_{m,n}`. -/
theorem ncard_gasm_eq_iff (hm : 2 ≤ m) (hn : 2 ≤ n) (b : Bdry m n) (hb : b.IsSigns) :
    (gasm b).ncard = N m n ↔ InFamily b := by
  by_cases hc : b.Closed
  · rw [ncard_gasm hm hn b hb hc,
      numExt_eq_N_iff m n hm hn _ (profile_isRingWalk hm hn b hb hc)]
    exact isFlat_profile_iff hm hn b hb hc
  · rw [gasm_eq_empty_of_not_closed (by omega) (by omega) b hb hc, Set.ncard_empty]
    constructor
    · intro h
      have := N_pos m n hm hn
      omega
    · intro h
      exact absurd (closed_of_inFamily hm hn b h) hc

end Max32
