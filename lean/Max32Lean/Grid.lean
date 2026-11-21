/-
Part B of `aristotle_request.md`: the grid, ring walks, and the main theorem on ring walks.
Paper: gasm_32_06, Sections 2 and 4 (Definition 2.3, Theorem 4.1).

Status: B1 (`numExt_of_flat`, `N_pos`) and B2 (`numExt_le_N`, `numExt_eq_N_iff`) are proved.
The numerical checks of Part D (`N_table`, `N_two`) are stated with `sorry`.
-/
import Mathlib
import Max32Lean.Fold

namespace Max32

variable (m n : ℕ)

/-- The vertices of the grid `G`: `{0,…,m} × {0,…,n}`. -/
abbrev Pt : Type := Fin (m + 1) × Fin (n + 1)

/-- The grid graph `G`: `(i,j)` and `(i',j')` are adjacent iff `|i - i'| + |j - j'| = 1`. -/
def gridGraph : SimpleGraph (Pt m n) :=
  SimpleGraph.fromRel fun p q =>
    (p.1 = q.1 ∧ p.2.val + 1 = q.2.val) ∨ (p.2 = q.2 ∧ p.1.val + 1 = q.1.val)

/-- The four corners `(0,0)`, `(0,n)`, `(m,0)`, `(m,n)`. -/
def IsCorner (p : Pt m n) : Prop :=
  (p.1.val = 0 ∨ p.1.val = m) ∧ (p.2.val = 0 ∨ p.2.val = n)

/-- The border of `G`: `i ∈ {0,m}` or `j ∈ {0,n}`. -/
def IsBorder (p : Pt m n) : Prop :=
  p.1.val = 0 ∨ p.1.val = m ∨ p.2.val = 0 ∨ p.2.val = n

/-- The vertex set of `Γ`: all vertices of `G` except the corners. -/
abbrev nonCorner : Set (Pt m n) := {p | ¬ IsCorner m n p}

/-- `Γ`: the grid with its four corners removed. -/
def Γ : SimpleGraph (nonCorner m n) := (gridGraph m n).induce (nonCorner m n)

/-- The ring `R`: the border vertices that are not corners. -/
def ringSet : Set (nonCorner m n) := {p | IsBorder m n p.1}

/-- A ring walk (Definition 2.3): `ρ(i,j) ≡ i + j (mod 2)` on the ring, and adjacent ring vertices
differ by 1. (`ρ` is a function on all of `Γ`; only its values on the ring are used.) -/
def IsRingWalk (ρ : nonCorner m n → ℤ) : Prop :=
  (∀ p ∈ ringSet m n, (ρ p - ((p.1.1.val : ℤ) + (p.1.2.val : ℤ))) % 2 = 0) ∧
    ∀ p ∈ ringSet m n, ∀ q ∈ ringSet m n, (Γ m n).Adj p q → |ρ p - ρ q| = 1

/-- A ring walk is flat if its range `max ρ - min ρ` is at most 1. -/
def IsFlat (ρ : nonCorner m n → ℤ) : Prop :=
  ∀ p ∈ ringSet m n, ∀ q ∈ ringSet m n, |ρ p - ρ q| ≤ 1

/-- The flat ring walk that is `0` on even and `1` on odd vertices (Corollary 5.1). -/
def parityWalk : nonCorner m n → ℤ :=
  fun p => (((p.1.1.val + p.1.2.val) % 2 : ℕ) : ℤ)

/-- `N(m,n)`: the number of height functions on `Γ` that are `0` on the even and `1` on the odd
ring vertices. -/
noncomputable def N : ℕ := numExt (Γ m n) (ringSet m n) (parityWalk m n)

/-! ### Geometry of the grid -/

/-- Adjacency in `Γ` in coordinates. -/
theorem adj_iff (p q : nonCorner m n) :
    (Γ m n).Adj p q ↔
      (p.1.1.val = q.1.1.val ∧ (p.1.2.val + 1 = q.1.2.val ∨ q.1.2.val + 1 = p.1.2.val)) ∨
      (p.1.2.val = q.1.2.val ∧ (p.1.1.val + 1 = q.1.1.val ∨ q.1.1.val + 1 = p.1.1.val)) := by
  obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hp⟩ := p
  obtain ⟨⟨⟨i', hi'⟩, ⟨j', hj'⟩⟩, hq⟩ := q
  show (gridGraph m n).Adj ((⟨i, hi⟩, ⟨j, hj⟩) : Pt m n) ((⟨i', hi'⟩, ⟨j', hj'⟩) : Pt m n) ↔ _
  unfold gridGraph
  rw [SimpleGraph.fromRel_adj]
  simp only [ne_eq, Prod.mk.injEq, Fin.mk.injEq]
  omega

/-- The vertex `(i,j)` of `Γ`. -/
def pt {m n : ℕ} (i j : ℕ) (hi : i ≤ m) (hj : j ≤ n)
    (hnc : ¬((i = 0 ∨ i = m) ∧ (j = 0 ∨ j = n))) : nonCorner m n :=
  ⟨(⟨i, Nat.lt_succ_of_le hi⟩, ⟨j, Nat.lt_succ_of_le hj⟩), hnc⟩

/-- A ring vertex has a neighbour in the interior. -/
theorem ring_has_interior_nbr (hm : 2 ≤ m) (hn : 2 ≤ n) (y : nonCorner m n)
    (hy : y ∈ ringSet m n) : ∃ x, x ∉ ringSet m n ∧ (Γ m n).Adj y x := by
  obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hnc⟩ := y
  have hnc' : ¬((i = 0 ∨ i = m) ∧ (j = 0 ∨ j = n)) := hnc
  have hy' : i = 0 ∨ i = m ∨ j = 0 ∨ j = n := hy
  rcases hy' with h | h | h | h
  · refine ⟨pt 1 j (by omega) (by omega) (by omega), ?_, ?_⟩
    · show ¬(1 = 0 ∨ 1 = m ∨ j = 0 ∨ j = n)
      omega
    · rw [adj_iff]
      dsimp [pt]
      omega
  · refine ⟨pt (m - 1) j (by omega) (by omega) (by omega), ?_, ?_⟩
    · show ¬(m - 1 = 0 ∨ m - 1 = m ∨ j = 0 ∨ j = n)
      omega
    · rw [adj_iff]
      dsimp [pt]
      omega
  · refine ⟨pt i 1 (by omega) (by omega) (by omega), ?_, ?_⟩
    · show ¬(i = 0 ∨ i = m ∨ 1 = 0 ∨ 1 = n)
      omega
    · rw [adj_iff]
      dsimp [pt]
      omega
  · refine ⟨pt i (n - 1) (by omega) (by omega) (by omega), ?_, ?_⟩
    · show ¬(i = 0 ∨ i = m ∨ n - 1 = 0 ∨ n - 1 = n)
      omega
    · rw [adj_iff]
      dsimp [pt]
      omega

section Interior

variable {m n}
variable (S : Set (nonCorner m n)) (hS : ∀ x, x ∉ ringSet m n → x ∈ S)

/-- The interior vertex `(i,j)`, as a vertex of the induced subgraph on `S`. -/
def spt (i j : ℕ) (h : 1 ≤ i ∧ i < m ∧ 1 ≤ j ∧ j < n) : S :=
  ⟨pt i j (by omega) (by omega) (by omega), hS _ (by
    show ¬(i = 0 ∨ i = m ∨ j = 0 ∨ j = n)
    omega)⟩

theorem spt_reach_row (i : ℕ) : ∀ (d : ℕ) (h : 1 ≤ i ∧ i < m ∧ 1 ≤ d + 1 ∧ d + 1 < n)
    (h1 : 1 ≤ i ∧ i < m ∧ 1 ≤ 1 ∧ 1 < n),
    ((Γ m n).induce S).Reachable (spt S hS i (d + 1) h) (spt S hS i 1 h1) := by
  intro d
  induction d with
  | zero => intro h h1; exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    intro h h1
    have hadj : ((Γ m n).induce S).Adj (spt S hS i (d + 1 + 1) h)
        (spt S hS i (d + 1) (by omega)) := by
      show (Γ m n).Adj _ _
      rw [adj_iff]
      dsimp [spt, pt]
      omega
    exact hadj.reachable.trans (ih (by omega) h1)

theorem spt_reach_col : ∀ (d : ℕ) (h : 1 ≤ d + 1 ∧ d + 1 < m ∧ 1 ≤ 1 ∧ 1 < n)
    (h1 : 1 ≤ 1 ∧ 1 < m ∧ 1 ≤ 1 ∧ 1 < n),
    ((Γ m n).induce S).Reachable (spt S hS (d + 1) 1 h) (spt S hS 1 1 h1) := by
  intro d
  induction d with
  | zero => intro h h1; exact SimpleGraph.Reachable.refl _
  | succ d ih =>
    intro h h1
    have hadj : ((Γ m n).induce S).Adj (spt S hS (d + 1 + 1) 1 h)
        (spt S hS (d + 1) 1 (by omega)) := by
      show (Γ m n).Adj _ _
      rw [adj_iff]
      dsimp [spt, pt]
      omega
    exact hadj.reachable.trans (ih (by omega) h1)

/-- Every interior vertex is joined to `(1,1)` inside the interior. -/
theorem interior_reach_base (x : nonCorner m n) (hx : x ∉ ringSet m n)
    (h1 : 1 ≤ 1 ∧ 1 < m ∧ 1 ≤ 1 ∧ 1 < n) :
    ((Γ m n).induce S).Reachable ⟨x, hS x hx⟩ (spt S hS 1 1 h1) := by
  obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hnc⟩ := x
  have hx' : ¬(i = 0 ∨ i = m ∨ j = 0 ∨ j = n) := hx
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  have r1 := spt_reach_row S hS (a + 1) b (by omega) (by omega)
  have r2 := spt_reach_col S hS a (by omega) h1
  exact r1.trans r2

/-- The interior `Λ` is connected, inside any set that contains it. -/
theorem interior_reachable (hm : 2 ≤ m) (hn : 2 ≤ n) (x x' : nonCorner m n)
    (hx : x ∉ ringSet m n) (hx' : x' ∉ ringSet m n) :
    ((Γ m n).induce S).Reachable ⟨x, hS x hx⟩ ⟨x', hS x' hx'⟩ :=
  (interior_reach_base S hS x hx (by omega)).trans
    (interior_reach_base S hS x' hx' (by omega)).symm

end Interior

/-- Every vertex of `Γ` is joined to a ring vertex, so Part A applies. -/
theorem ring_meets_components (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ x : nonCorner m n, ∃ y ∈ ringSet m n, (Γ m n).Reachable x y := by
  intro x
  by_cases hx : x ∈ ringSet m n
  · exact ⟨x, hx, SimpleGraph.Reachable.refl _⟩
  · have hr : (pt 1 0 (by omega) (by omega) (by omega) : nonCorner m n) ∈ ringSet m n := by
      show (1 = 0 ∨ 1 = m ∨ 0 = 0 ∨ 0 = n)
      omega
    obtain ⟨z, hz, hadj⟩ := ring_has_interior_nbr m n hm hn _ hr
    refine ⟨_, hr, ?_⟩
    have r := interior_reachable (Set.univ) (fun _ _ => Set.mem_univ _) hm hn x z hx hz
    have r' := r.map (SimpleGraph.Embedding.induce (G := Γ m n) Set.univ).toHom
    exact r'.trans hadj.symm.reachable

/-! ### Ring walks -/

/-- The fold of a ring walk is a ring walk. -/
theorem isRingWalk_fold (ρ : nonCorner m n → ℤ) (hρ : IsRingWalk m n ρ) (k : ℤ) :
    IsRingWalk m n (foldFn k ρ) := by
  constructor
  · intro p hp
    have h := hρ.1 p hp
    show (fold k (ρ p) - ((p.1.1.val : ℤ) + (p.1.2.val : ℤ))) % 2 = 0
    rcases le_total (ρ p) k with c | c
    · rw [fold_of_le c]; exact h
    · rw [fold_of_ge c]; omega
  · intro p hp q hq hpq
    exact abs_fold_sub_fold k (hρ.2 p hp q hq hpq)

/-- **B1.** All flat ring walks have the same number of extensions, `N(m,n)`. -/
theorem numExt_of_flat (hm : 2 ≤ m) (hn : 2 ≤ n) (ρ : nonCorner m n → ℤ)
    (hρ : IsRingWalk m n ρ) (hflat : IsFlat m n ρ) :
    numExt (Γ m n) (ringSet m n) ρ = N m n := by
  have hp0 : (pt 0 1 (by omega) (by omega) (by omega) : nonCorner m n) ∈ ringSet m n := by
    show (0 = 0 ∨ 0 = m ∨ 1 = 0 ∨ 1 = n)
    omega
  generalize hv : ρ (pt 0 1 (by omega) (by omega) (by omega)) = v at *
  have hpar0 : (v - 1) % 2 = 0 := by
    have h := hρ.1 _ hp0
    rw [hv] at h
    dsimp [pt] at h
    omega
  -- the facts available at every ring vertex
  have hfact : ∀ q ∈ ringSet m n,
      (ρ q - ((q.1.1.val : ℤ) + (q.1.2.val : ℤ))) % 2 = 0 ∧ -1 ≤ ρ q - v ∧ ρ q - v ≤ 1 := by
    intro q hq
    have h1 := hρ.1 q hq
    have h2 := abs_le.mp (hflat q hq _ hp0)
    rw [hv] at h2
    exact ⟨h1, h2.1, h2.2⟩
  unfold N
  by_cases hE : ∀ q ∈ ringSet m n, (q.1.1.val + q.1.2.val) % 2 = 0 → ρ q = v - 1
  · have hc : ∀ q ∈ ringSet m n, ρ q = parityWalk m n q + (v - 1) := by
      intro q hq
      obtain ⟨f1, f2, f3⟩ := hfact q hq
      show ρ q = (((q.1.1.val + q.1.2.val) % 2 : ℕ) : ℤ) + (v - 1)
      by_cases he : (q.1.1.val + q.1.2.val) % 2 = 0
      · have := hE q hq he
        omega
      · omega
    have e1 : numExt (Γ m n) (ringSet m n) ρ =
        numExt (Γ m n) (ringSet m n) (fun x => parityWalk m n x + (v - 1)) := by
      unfold numExt
      rw [ext_congr hc]
    rw [e1]
    exact numExt_map (Γ m n) (ringSet m n) (parityWalk m n) (fun a => a + (v - 1))
      (fun a => a - (v - 1)) (fun a => by ring) (fun a => by ring)
      (fun a b => by rw [show a + (v - 1) - (b + (v - 1)) = a - b by ring])
  · push Not at hE
    obtain ⟨q0, hq0, he0, hne0⟩ := hE
    obtain ⟨g1, g2, g3⟩ := hfact q0 hq0
    have hq0v : ρ q0 = v + 1 := by omega
    have hc : ∀ q ∈ ringSet m n, ρ q = (v + 1) - parityWalk m n q := by
      intro q hq
      obtain ⟨f1, f2, f3⟩ := hfact q hq
      have h3 := abs_le.mp (hflat q hq q0 hq0)
      show ρ q = (v + 1) - (((q.1.1.val + q.1.2.val) % 2 : ℕ) : ℤ)
      omega
    have e1 : numExt (Γ m n) (ringSet m n) ρ =
        numExt (Γ m n) (ringSet m n) (fun x => (v + 1) - parityWalk m n x) := by
      unfold numExt
      rw [ext_congr hc]
    rw [e1]
    exact numExt_map (Γ m n) (ringSet m n) (parityWalk m n) (fun a => (v + 1) - a)
      (fun a => (v + 1) - a) (fun a => by ring) (fun a => by ring)
      (fun a b => by rw [show v + 1 - a - (v + 1 - b) = -(a - b) by ring, abs_neg])

/-- The walk `parityWalk` extends to a height function: itself. -/
theorem parityWalk_mem : parityWalk m n ∈ Ext (Γ m n) (ringSet m n) (parityWalk m n) := by
  refine ⟨fun x y hxy => ?_, fun _ _ => rfl⟩
  have h := (adj_iff m n x y).mp hxy
  show |(((x.1.1.val + x.1.2.val) % 2 : ℕ) : ℤ) - (((y.1.1.val + y.1.2.val) % 2 : ℕ) : ℤ)| = 1
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  omega

/-- **B1.** `N(m,n)` is positive. -/
theorem N_pos (hm : 2 ≤ m) (hn : 2 ≤ n) : 0 < N m n :=
  (Set.ncard_pos (ext_finite (Γ m n) (ringSet m n) (ring_meets_components m n hm hn) _)).mpr
    ⟨_, parityWalk_mem m n⟩

/-! ### The strict step -/

open Classical in
/-- The function `g` of the proof of Theorem 4.1: the folded walk on the ring, and the two values
`F_k ρ(p)`, `F_k ρ(p) - 1` in the interior, by parity. Here `p` is a ring vertex with `ρ p > k`. -/
noncomputable def strictG (ρ : nonCorner m n → ℤ) (k : ℤ) (p : nonCorner m n) :
    nonCorner m n → ℤ := fun x =>
  if x ∈ ringSet m n then fold k (ρ x)
  else if (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0 then 2 * k - ρ p
  else 2 * k - ρ p - 1

theorem strictG_ring {ρ : nonCorner m n → ℤ} {k : ℤ} {p x : nonCorner m n}
    (hx : x ∈ ringSet m n) : strictG m n ρ k p x = fold k (ρ x) := by
  simp [strictG, hx]

theorem strictG_even {ρ : nonCorner m n → ℤ} {k : ℤ} {p x : nonCorner m n}
    (hx : x ∉ ringSet m n) (he : (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0) :
    strictG m n ρ k p x = 2 * k - ρ p := by
  simp [strictG, hx, he]

theorem strictG_odd {ρ : nonCorner m n → ℤ} {k : ℤ} {p x : nonCorner m n}
    (hx : x ∉ ringSet m n) (he : ¬ (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0) :
    strictG m n ρ k p x = 2 * k - ρ p - 1 := by
  simp [strictG, hx, he]

/-- If a ring walk is not flat but one of its folds is flat, it has fewer than `N(m,n)`
extensions. (For range 2 this is the last step of the proof of Theorem 4.1.) -/
theorem lt_N_of_fold_flat (hm : 2 ≤ m) (hn : 2 ≤ n) (ρ : nonCorner m n → ℤ)
    (hρ : IsRingWalk m n ρ) (k : ℤ) (hf : IsFlat m n (foldFn k ρ)) (hnf : ¬ IsFlat m n ρ) :
    numExt (Γ m n) (ringSet m n) ρ < N m n := by
  have hρ' := isRingWalk_fold m n ρ hρ k
  rw [← numExt_of_flat m n hm hn (foldFn k ρ) hρ' hf]
  have hp : ∃ p ∈ ringSet m n, k < ρ p := by
    by_contra hc
    push Not at hc
    apply hnf
    intro a ha b hb
    have h := hf a ha b hb
    have e1 : foldFn k ρ a = ρ a := fold_of_le (hc a ha)
    have e2 : foldFn k ρ b = ρ b := fold_of_le (hc b hb)
    rw [e1, e2] at h
    exact h
  have hq : ∃ q ∈ ringSet m n, ρ q < k := by
    by_contra hc
    push Not at hc
    apply hnf
    intro a ha b hb
    have h := hf a ha b hb
    have e1 : foldFn k ρ a = 2 * k - ρ a := fold_of_ge (hc a ha)
    have e2 : foldFn k ρ b = 2 * k - ρ b := fold_of_ge (hc b hb)
    rw [e1, e2, abs_le] at h
    rw [abs_le]
    constructor <;> omega
  obtain ⟨p, hpR, hpk⟩ := hp
  obtain ⟨q, hqR, hqk⟩ := hq
  -- facts about the folded walk on the ring
  have hFp : fold k (ρ p) = 2 * k - ρ p := fold_of_ge hpk.le
  have hparp : (2 * k - ρ p - ((p.1.1.val : ℤ) + (p.1.2.val : ℤ))) % 2 = 0 := by
    have h : (fold k (ρ p) - ((p.1.1.val : ℤ) + (p.1.2.val : ℤ))) % 2 = 0 := hρ'.1 p hpR
    rw [hFp] at h
    exact h
  have hfact : ∀ y ∈ ringSet m n,
      (fold k (ρ y) - ((y.1.1.val : ℤ) + (y.1.2.val : ℤ))) % 2 = 0 ∧
        -1 ≤ fold k (ρ y) - (2 * k - ρ p) ∧ fold k (ρ y) - (2 * k - ρ p) ≤ 1 := by
    intro y hy
    have h1 : (fold k (ρ y) - ((y.1.1.val : ℤ) + (y.1.2.val : ℤ))) % 2 = 0 := hρ'.1 y hy
    have h2 : |fold k (ρ y) - fold k (ρ p)| ≤ 1 := hf y hy p hpR
    rw [hFp, abs_le] at h2
    exact ⟨h1, h2.1, h2.2⟩
  have hgH : IsHeight (Γ m n) (strictG m n ρ k p) := by
    intro x y hxy
    have hadj := (adj_iff m n x y).mp hxy
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
    by_cases hx : x ∈ ringSet m n <;> by_cases hy : y ∈ ringSet m n
    · have h : |fold k (ρ x) - fold k (ρ y)| = 1 := hρ'.2 x hx y hy hxy
      rw [strictG_ring m n hx, strictG_ring m n hy]
      exact (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp h
    · obtain ⟨f1, f2, f3⟩ := hfact x hx
      by_cases he : (y.1.1.val + y.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0
      · rw [strictG_ring m n hx, strictG_even m n hy he]; omega
      · rw [strictG_ring m n hx, strictG_odd m n hy he]; omega
    · obtain ⟨f1, f2, f3⟩ := hfact y hy
      by_cases he : (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0
      · rw [strictG_even m n hx he, strictG_ring m n hy]; omega
      · rw [strictG_odd m n hx he, strictG_ring m n hy]; omega
    · by_cases he : (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0
      · have he' : ¬ (y.1.1.val + y.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0 := by omega
        rw [strictG_even m n hx he, strictG_odd m n hy he']; omega
      · have he' : (y.1.1.val + y.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0 := by omega
        rw [strictG_odd m n hx he, strictG_even m n hy he']; omega
  have hgle : ∀ x, strictG m n ρ k p x ≤ k := by
    intro x
    by_cases hx : x ∈ ringSet m n
    · rw [strictG_ring m n hx]; exact fold_le _ _
    · by_cases he : (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0
      · rw [strictG_even m n hx he]; omega
      · rw [strictG_odd m n hx he]; omega
  have hgmem : strictG m n ρ k p ∈ foldTargets (Γ m n) (ringSet m n) ρ k :=
    ⟨⟨hgH, fun x hx => by rw [strictG_ring m n hx]; rfl⟩, hgle⟩
  have hS : ∀ x, x ∉ ringSet m n → x ∈ lowSet (strictG m n ρ k p) k := by
    intro x hx
    show strictG m n ρ k p x < k
    by_cases he : (x.1.1.val + x.1.2.val + p.1.1.val + p.1.2.val) % 2 = 0
    · rw [strictG_even m n hx he]; omega
    · rw [strictG_odd m n hx he]; omega
  have hqlow : q ∈ lowSet (strictG m n ρ k p) k := by
    show strictG m n ρ k p q < k
    rw [strictG_ring m n hqR, fold_of_le hqk.le]
    exact hqk
  have hplow : p ∈ lowSet (strictG m n ρ k p) k := by
    show strictG m n ρ k p p < k
    rw [strictG_ring m n hpR, hFp]
    omega
  refine fold_inequality_strict (Γ m n) (ringSet m n) (ring_meets_components m n hm hn) ρ k
    (strictG m n ρ k p) hgmem ?_
  intro hadm
  obtain ⟨xq, hxq, hadjq⟩ := ring_has_interior_nbr m n hm hn q hqR
  obtain ⟨xp, hxp, hadjp⟩ := ring_has_interior_nbr m n hm hn p hpR
  have r1 : ((Γ m n).induce (lowSet (strictG m n ρ k p) k)).Reachable ⟨q, hqlow⟩
      ⟨xq, hS xq hxq⟩ :=
    SimpleGraph.Adj.reachable (show ((Γ m n).induce _).Adj ⟨q, hqlow⟩ ⟨xq, hS xq hxq⟩ from hadjq)
  have r2 := interior_reachable (lowSet (strictG m n ρ k p) k) hS hm hn xq xp hxq hxp
  have r3 : ((Γ m n).induce (lowSet (strictG m n ρ k p) k)).Reachable ⟨xp, hS xp hxp⟩
      ⟨p, hplow⟩ :=
    SimpleGraph.Adj.reachable
      (show ((Γ m n).induce _).Adj ⟨xp, hS xp hxp⟩ ⟨p, hplow⟩ from hadjp.symm)
  exact hadm ⟨q, hqlow⟩ ⟨p, hplow⟩ hqR hpR hqk hpk ((r1.trans r2).trans r3)

/-! ### Theorem 4.1 -/

/-- A ring walk that is not flat has fewer than `N(m,n)` extensions. The induction is on a bound
`d` for the range: fold at `max ρ - 1`. -/
theorem lt_N_of_not_flat (hm : 2 ≤ m) (hn : 2 ≤ n) : ∀ (d : ℕ) (ρ : nonCorner m n → ℤ),
    IsRingWalk m n ρ → (∀ p ∈ ringSet m n, ∀ q ∈ ringSet m n, ρ p - ρ q ≤ (d : ℤ)) →
    ¬ IsFlat m n ρ → numExt (Γ m n) (ringSet m n) ρ < N m n := by
  intro d
  induction d with
  | zero =>
    intro ρ hρ hb hnf
    exfalso
    apply hnf
    intro a ha b hb2
    have h1 := hb a ha b hb2
    have h2 := hb b hb2 a ha
    rw [abs_le]
    push_cast at h1 h2
    constructor <;> omega
  | succ d ih =>
    intro ρ hρ hb hnf
    by_cases hb' : ∀ p ∈ ringSet m n, ∀ q ∈ ringSet m n, ρ p - ρ q ≤ (d : ℤ)
    · exact ih ρ hρ hb' hnf
    · push Not at hb'
      obtain ⟨p, hp, q, hq, hpq⟩ := hb'
      have hd1 : 1 ≤ d := by
        by_contra hd
        apply hnf
        intro a ha b hb2
        have h1 := hb a ha b hb2
        have h2 := hb b hb2 a ha
        rw [abs_le]
        push_cast at h1 h2
        constructor <;> omega
      have e : ρ p - ρ q = (d : ℤ) + 1 := by
        have h1 := hb p hp q hq
        push_cast at h1
        omega
      have hmax : ∀ r ∈ ringSet m n, ρ r ≤ ρ p := by
        intro r hr
        have h1 := hb r hr q hq
        push_cast at h1
        omega
      have hmin : ∀ r ∈ ringSet m n, ρ p - ((d : ℤ) + 1) ≤ ρ r := by
        intro r hr
        have h1 := hb p hp r hr
        push_cast at h1
        omega
      have hρ' := isRingWalk_fold m n ρ hρ (ρ p - 1)
      have hb'' : ∀ r ∈ ringSet m n, ∀ s ∈ ringSet m n,
          foldFn (ρ p - 1) ρ r - foldFn (ρ p - 1) ρ s ≤ (d : ℤ) := by
        intro r hr s hs
        have h1 : fold (ρ p - 1) (ρ r) ≤ ρ p - 1 := fold_le _ _
        have h2 : ρ p - ((d : ℤ) + 1) ≤ fold (ρ p - 1) (ρ s) := by
          rcases le_total (ρ s) (ρ p - 1) with c | c
          · rw [fold_of_le c]; exact hmin s hs
          · rw [fold_of_ge c]
            have := hmax s hs
            omega
        show fold (ρ p - 1) (ρ r) - fold (ρ p - 1) (ρ s) ≤ (d : ℤ)
        omega
      have hle := fold_inequality (Γ m n) (ringSet m n) (ring_meets_components m n hm hn) ρ
        (ρ p - 1)
      by_cases hf : IsFlat m n (foldFn (ρ p - 1) ρ)
      · exact lt_N_of_fold_flat m n hm hn ρ hρ (ρ p - 1) hf hnf
      · exact lt_of_le_of_lt hle (ih _ hρ' hb'' hf)

/-- Every function on the (finite) vertex set has a bounded range. -/
theorem exists_bound (ρ : nonCorner m n → ℤ) :
    ∃ d : ℕ, ∀ p ∈ ringSet m n, ∀ q ∈ ringSet m n, ρ p - ρ q ≤ (d : ℤ) := by
  obtain ⟨B, hB⟩ := (Set.finite_range
    (fun pq : nonCorner m n × nonCorner m n => ρ pq.1 - ρ pq.2)).bddAbove
  refine ⟨B.toNat, fun p _ q _ => ?_⟩
  have h : ρ p - ρ q ≤ B := hB (Set.mem_range_self (p, q))
  omega

/-- **B2 (Theorem 4.1), equality case.** -/
theorem numExt_eq_N_iff (hm : 2 ≤ m) (hn : 2 ≤ n) (ρ : nonCorner m n → ℤ)
    (hρ : IsRingWalk m n ρ) :
    numExt (Γ m n) (ringSet m n) ρ = N m n ↔ IsFlat m n ρ := by
  constructor
  · intro h
    by_contra hnf
    obtain ⟨d, hd⟩ := exists_bound m n ρ
    have := lt_N_of_not_flat m n hm hn d ρ hρ hd hnf
    omega
  · exact numExt_of_flat m n hm hn ρ hρ

/-- **B2 (Theorem 4.1), inequality.** -/
theorem numExt_le_N (hm : 2 ≤ m) (hn : 2 ≤ n) (ρ : nonCorner m n → ℤ)
    (hρ : IsRingWalk m n ρ) :
    numExt (Γ m n) (ringSet m n) ρ ≤ N m n := by
  by_cases hf : IsFlat m n ρ
  · exact (numExt_of_flat m n hm hn ρ hρ hf).le
  · obtain ⟨d, hd⟩ := exists_bound m n ρ
    exact (lt_N_of_not_flat m n hm hn d ρ hρ hd hf).le

/-! ### Part D (optional numerical checks) -/

/-- Table 1: `N(n,n)` for `n = 2,…,6`. -/
theorem N_table :
    N 2 2 = 2 ∧ N 3 3 = 7 ∧ N 4 4 = 64 ∧ N 5 5 = 1322 ∧ N 6 6 = 64914 := by
  sorry

/-- `N(2,n)` is the Fibonacci number `fib (n+1)`. -/
theorem N_two (hn : 2 ≤ n) : N 2 n = Nat.fib (n + 1) := by
  sorry

end Max32
