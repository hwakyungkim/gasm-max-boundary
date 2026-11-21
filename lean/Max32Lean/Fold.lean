/-
Part A of `aristotle_request.md`: folding on a graph.
Paper: gasm_32_06, Section 3 (Lemma 3.1 and Theorem 3.2).

Status: A1, A2, A3, the finiteness of `Ext`, A4 (`fold_inequality`) and the strict form
(`fold_inequality_strict`) are proved. The two fibre formulas of A5 are stated with `sorry`.

A4 is proved directly, without A5: `foldLift` is an injection `Ext ρ → Ext (F_k ∘ ρ)`. It keeps `h`
on the components of `{F_k h < k}` that contain no vertex of `R`, and replaces `h` by `F_k h`
elsewhere.
-/
import Mathlib

open BigOperators

namespace Max32

/-! ### The fold -/

/-- The fold at level `k`: `F_k(x) = k - |x - k|`. -/
def fold (k x : ℤ) : ℤ := k - |x - k|

theorem fold_of_le {k x : ℤ} (h : x ≤ k) : fold k x = x := by
  unfold fold
  rw [abs_of_nonpos (sub_nonpos.mpr h)]
  ring

theorem fold_of_ge {k x : ℤ} (h : k ≤ x) : fold k x = 2 * k - x := by
  unfold fold
  rw [abs_of_nonneg (sub_nonneg.mpr h)]
  ring

theorem fold_le (k x : ℤ) : fold k x ≤ k := by
  rcases le_total x k with h | h
  · rw [fold_of_le h]; exact h
  · rw [fold_of_ge h]; omega

/-- Folding twice at the same level is folding once (used as `F_k ρ' = F_k ρ` in Theorem 3.2). -/
theorem fold_fold_le (k x : ℤ) : fold k (fold k x) = fold k x :=
  fold_of_le (fold_le k x)

/-- If `F_k(x) < k` then `x ≠ k`. -/
theorem ne_of_fold_lt {k x : ℤ} (h : fold k x < k) : x ≠ k := by
  intro hx
  rw [hx, fold_of_le le_rfl] at h
  exact lt_irrefl _ h

/-! ### Height functions -/

variable {V : Type*}

/-- A height function on a graph: adjacent vertices differ by exactly 1. -/
def IsHeight (Γ : SimpleGraph V) (h : V → ℤ) : Prop :=
  ∀ x y, Γ.Adj x y → |h x - h y| = 1

/-- The fold of a function, `F_k h = F_k ∘ h`. -/
def foldFn (k : ℤ) (h : V → ℤ) : V → ℤ := fun x => fold k (h x)

/-- The set `{x | g x < k}`. -/
def lowSet (g : V → ℤ) (k : ℤ) : Set V := {x | g x < k}

/-- Folding keeps two integers that differ by 1 at distance 1. -/
theorem abs_fold_sub_fold {a b : ℤ} (k : ℤ) (h : |a - b| = 1) : |fold k a - fold k b| = 1 := by
  have h1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp h
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  rcases le_total a k with hx | hx <;> rcases le_total b k with hy | hy
  · rw [fold_of_le hx, fold_of_le hy]; omega
  · rw [fold_of_le hx, fold_of_ge hy]; omega
  · rw [fold_of_ge hx, fold_of_le hy]; omega
  · rw [fold_of_ge hx, fold_of_ge hy]; omega

/-- **A1 (Lemma 3.1(a)), first half.** The fold of a height function is a height function. -/
theorem isHeight_fold {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (k : ℤ) :
    IsHeight Γ (foldFn k h) := by
  intro x y hxy
  have h1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (hh x y hxy)
  show |fold k (h x) - fold k (h y)| = 1
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  rcases le_total (h x) k with hx | hx <;> rcases le_total (h y) k with hy | hy
  · rw [fold_of_le hx, fold_of_le hy]; omega
  · rw [fold_of_le hx, fold_of_ge hy]; omega
  · rw [fold_of_ge hx, fold_of_le hy]; omega
  · rw [fold_of_ge hx, fold_of_ge hy]; omega

/-- **A1 (Lemma 3.1(a)), second half.** `F_k h ≤ k` pointwise. -/
theorem foldFn_le (k : ℤ) (h : V → ℤ) (x : V) : foldFn k h x ≤ k :=
  fold_le k (h x)

/-- The sign of `h - k` is constant along a path that avoids the level `k`.
This is the core of Lemma 3.1(b). -/
theorem sign_const {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) {k : ℤ} (S : Set V)
    (hS : ∀ x ∈ S, h x ≠ k) (x y : S) (hxy : (Γ.induce S).Reachable x y) :
    h x.1 < k ↔ h y.1 < k := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Iff.rfl
  | @cons u v w hadj _ ih =>
    have hadj' : Γ.Adj u.1 v.1 := hadj
    have h1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (hh _ _ hadj')
    have hu := hS u.1 u.2
    have hv := hS v.1 v.2
    rw [← ih]
    constructor <;> intro _ <;> omega

/-- **A2 (Lemma 3.1(b)).** On a connected component of `{g < k}`, where `g = F_k h`,
either `h = g` or `h = 2k - g`. -/
theorem fold_component {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (k : ℤ)
    (x y : lowSet (foldFn k h) k)
    (hxy : (Γ.induce (lowSet (foldFn k h) k)).Reachable x y) :
    (h x.1 = foldFn k h x.1 ∧ h y.1 = foldFn k h y.1) ∨
      (h x.1 = 2 * k - foldFn k h x.1 ∧ h y.1 = 2 * k - foldFn k h y.1) := by
  have hS : ∀ z ∈ lowSet (foldFn k h) k, h z ≠ k :=
    fun z hz => ne_of_fold_lt (show fold k (h z) < k from hz)
  have s := sign_const hh (lowSet (foldFn k h) k) hS x y hxy
  have hx := hS x.1 x.2
  have hy := hS y.1 y.2
  show (h x.1 = fold k (h x.1) ∧ h y.1 = fold k (h y.1)) ∨
      (h x.1 = 2 * k - fold k (h x.1) ∧ h y.1 = 2 * k - fold k (h y.1))
  by_cases c : h x.1 < k
  · have c' := s.mp c
    left
    rw [fold_of_le c.le, fold_of_le c'.le]
    exact ⟨rfl, rfl⟩
  · have c' : ¬ h y.1 < k := fun hc => c (s.mpr hc)
    right
    rw [fold_of_ge (by omega), fold_of_ge (by omega)]
    constructor <;> ring

open Classical in
/-- Reflect `g` at level `k` on the set `T`: `2k - g` on `T`, `g` elsewhere. -/
noncomputable def reflectOn (k : ℤ) (g : V → ℤ) (T : Set V) : V → ℤ :=
  fun x => if x ∈ T then 2 * k - g x else g x

theorem reflectOn_pos {k : ℤ} {g : V → ℤ} {T : Set V} {x : V} (hx : x ∈ T) :
    reflectOn k g T x = 2 * k - g x := by
  unfold reflectOn
  simp [hx]

theorem reflectOn_neg {k : ℤ} {g : V → ℤ} {T : Set V} {x : V} (hx : x ∉ T) :
    reflectOn k g T x = g x := by
  unfold reflectOn
  simp [hx]

/-- `T` is a union of connected components of the induced subgraph on `{g < k}`. -/
def IsUnionOfComponents (Γ : SimpleGraph V) (g : V → ℤ) (k : ℤ) (T : Set V) : Prop :=
  T ⊆ lowSet g k ∧
    ∀ x y : lowSet g k, (Γ.induce (lowSet g k)).Reachable x y → x.1 ∈ T → y.1 ∈ T

/-- **A3 (Lemma 3.1(c)).** Reflecting a union of components of `{g < k}` gives a height function
whose fold is `g`. -/
theorem reflectOn_isHeight {Γ : SimpleGraph V} {g : V → ℤ} (hg : IsHeight Γ g) (k : ℤ)
    (hgk : ∀ x, g x ≤ k) (T : Set V) (hT : IsUnionOfComponents Γ g k T) :
    IsHeight Γ (reflectOn k g T) ∧ foldFn k (reflectOn k g T) = g := by
  obtain ⟨hTS, hTc⟩ := hT
  have key : ∀ x y, Γ.Adj x y → x ∈ T → y ∉ T → g y = k := by
    intro x y hxy hx hy
    by_contra hne
    have hylow : y ∈ lowSet g k := show g y < k from lt_of_le_of_ne (hgk y) hne
    have hadj : (Γ.induce (lowSet g k)).Adj ⟨x, hTS hx⟩ ⟨y, hylow⟩ := hxy
    exact hy (hTc ⟨x, hTS hx⟩ ⟨y, hylow⟩ hadj.reachable hx)
  constructor
  · intro x y hxy
    have h1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (hg x y hxy)
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
    by_cases hx : x ∈ T <;> by_cases hy : y ∈ T
    · rw [reflectOn_pos hx, reflectOn_pos hy]; omega
    · have h2 := key x y hxy hx hy
      have hxl : g x < k := hTS hx
      rw [reflectOn_pos hx, reflectOn_neg hy]; omega
    · have h2 := key y x hxy.symm hy hx
      have hyl : g y < k := hTS hy
      rw [reflectOn_neg hx, reflectOn_pos hy]; omega
    · rw [reflectOn_neg hx, reflectOn_neg hy]; omega
  · funext x
    show fold k (reflectOn k g T x) = g x
    by_cases hx : x ∈ T
    · have hxl : g x < k := hTS hx
      rw [reflectOn_pos hx, fold_of_ge (by omega)]; ring
    · rw [reflectOn_neg hx, fold_of_le (hgk x)]

/-! ### Extensions of a boundary function -/

/-- `Ext ρ`: the height functions on `Γ` that agree with `ρ` on `R`.
(`ρ` is a function on all of `V`; only its values on `R` are used.) -/
def Ext (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) : Set (V → ℤ) :=
  {h | IsHeight Γ h ∧ ∀ x ∈ R, h x = ρ x}

/-- `f ρ = |Ext ρ|`. -/
noncomputable def numExt (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) : ℕ :=
  (Ext Γ R ρ).ncard

/-- Along a walk a height function changes by at most the length of the walk. -/
theorem isHeight_abs_sub_le_length {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h)
    {x y : V} (p : Γ.Walk x y) : |h x - h y| ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons u v w hadj p ih =>
    have h1 := hh _ _ hadj
    have h2 := abs_sub_le (h u) (h v) (h w)
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    linarith

/-- `Ext ρ` is finite when every connected component of `Γ` meets `R`. -/
theorem ext_finite [Finite V] (Γ : SimpleGraph V) (R : Set V)
    (hR : ∀ x : V, ∃ y ∈ R, Γ.Reachable x y) (ρ : V → ℤ) :
    (Ext Γ R ρ).Finite := by
  choose y hyR hreach using hR
  refine (Set.Finite.pi (fun x => Set.finite_Icc
    (ρ (y x) - ((hreach x).some.length : ℤ)) (ρ (y x) + ((hreach x).some.length : ℤ)))).subset ?_
  intro h hh x _
  have h1 := isHeight_abs_sub_le_length hh.1 (hreach x).some
  rw [hh.2 _ (hyR x)] at h1
  have h2 := abs_le.mp h1
  exact ⟨by linarith [h2.2], by linarith [h2.1]⟩

/-- `Ext ρ` depends only on the values of `ρ` on `R`. -/
theorem ext_congr {Γ : SimpleGraph V} {R : Set V} {ρ ρ' : V → ℤ} (h : ∀ x ∈ R, ρ x = ρ' x) :
    Ext Γ R ρ = Ext Γ R ρ' := by
  ext f
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, fun x hx => (b x hx).trans (h x hx)⟩
  · rintro ⟨a, b⟩
    exact ⟨a, fun x hx => (b x hx).trans (h x hx).symm⟩

/-- `f` does not change when `ρ` is composed with an isometry of `ℤ`
(a translation `x ↦ x + c` or a reflection `x ↦ c - x`). -/
theorem numExt_map (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (φ ψ : ℤ → ℤ)
    (h1 : ∀ a, φ (ψ a) = a) (h2 : ∀ a, ψ (φ a) = a) (hφ : ∀ a b, |φ a - φ b| = |a - b|) :
    numExt Γ R (fun x => φ (ρ x)) = numExt Γ R ρ := by
  have hψ : ∀ a b, |ψ a - ψ b| = |a - b| := fun a b => by rw [← hφ (ψ a) (ψ b), h1, h1]
  have himg : Ext Γ R (fun x => φ (ρ x)) = (fun h : V → ℤ => fun x => φ (h x)) '' Ext Γ R ρ := by
    ext g
    constructor
    · rintro ⟨hg, hgR⟩
      refine ⟨fun x => ψ (g x), ⟨fun x y hxy => ?_, fun x hx => ?_⟩, ?_⟩
      · show |ψ (g x) - ψ (g y)| = 1
        rw [hψ]
        exact hg x y hxy
      · show ψ (g x) = ρ x
        have e : g x = φ (ρ x) := hgR x hx
        rw [e]
        exact h2 _
      · funext x
        exact h1 _
    · rintro ⟨h, ⟨hh, hhR⟩, rfl⟩
      refine ⟨fun x y hxy => ?_, fun x hx => ?_⟩
      · show |φ (h x) - φ (h y)| = 1
        rw [hφ]
        exact hh x y hxy
      · show φ (h x) = φ (ρ x)
        rw [hhR x hx]
  unfold numExt
  rw [himg]
  refine Set.ncard_image_of_injective _ (fun a b hab => ?_)
  funext x
  have e : φ (a x) = φ (b x) := congrFun hab x
  calc a x = ψ (φ (a x)) := (h2 _).symm
    _ = ψ (φ (b x)) := by rw [e]
    _ = b x := h2 _

/-! ### The injection `Ext ρ → Ext (F_k ∘ ρ)` -/

/-- The vertices of `{g < k}` where `h > k` and whose component contains no vertex of `R`. -/
def liftSet (Γ : SimpleGraph V) (R : Set V) (k : ℤ) (g h : V → ℤ) : Set V :=
  {x | ∃ hx : x ∈ lowSet g k, k < h x ∧
    ∀ y : lowSet g k, y.1 ∈ R → ¬ (Γ.induce (lowSet g k)).Reachable ⟨x, hx⟩ y}

/-- Fold `h` on the components that contain a vertex of `R`, keep it on the others. -/
noncomputable def foldLift (Γ : SimpleGraph V) (R : Set V) (k : ℤ) (h : V → ℤ) : V → ℤ :=
  reflectOn k (foldFn k h) (liftSet Γ R k (foldFn k h) h)

theorem liftSet_isUnion {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (R : Set V) (k : ℤ) :
    IsUnionOfComponents Γ (foldFn k h) k (liftSet Γ R k (foldFn k h) h) := by
  have hS : ∀ z ∈ lowSet (foldFn k h) k, h z ≠ k :=
    fun z hz => ne_of_fold_lt (show fold k (h z) < k from hz)
  constructor
  · rintro x ⟨hx, -⟩
    exact hx
  · rintro x y hxy ⟨hx, hlt, hfree⟩
    have s := sign_const hh (lowSet (foldFn k h) k) hS x y hxy
    have hy := hS y.1 y.2
    refine ⟨y.2, ?_, ?_⟩
    · by_contra hc
      have hyk : h y.1 < k := by omega
      have hxk := s.mpr hyk
      omega
    · intro z hz hyz
      exact hfree z hz (hxy.trans hyz)

theorem foldFn_foldLift {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (R : Set V) (k : ℤ) :
    foldFn k (foldLift Γ R k h) = foldFn k h :=
  (reflectOn_isHeight (isHeight_fold hh k) k (foldFn_le k h) _ (liftSet_isUnion hh R k)).2

theorem foldLift_mem {Γ : SimpleGraph V} {R : Set V} {ρ h : V → ℤ} (k : ℤ)
    (hh : h ∈ Ext Γ R ρ) : foldLift Γ R k h ∈ Ext Γ R (foldFn k ρ) := by
  refine ⟨(reflectOn_isHeight (isHeight_fold hh.1 k) k (foldFn_le k h) _
    (liftSet_isUnion hh.1 R k)).1, ?_⟩
  intro x hxR
  have hx : x ∉ liftSet Γ R k (foldFn k h) h := by
    rintro ⟨hx, -, hfree⟩
    exact hfree ⟨x, hx⟩ hxR (SimpleGraph.Reachable.refl _)
  show reflectOn k (foldFn k h) (liftSet Γ R k (foldFn k h) h) x = fold k (ρ x)
  rw [reflectOn_neg hx, ← hh.2 x hxR]
  rfl

/-- On a component without a vertex of `R`, `foldLift` does not change `h`. -/
theorem reflectOn_liftSet_eq {Γ : SimpleGraph V} (R : Set V) (k : ℤ) (g h : V → ℤ)
    (hg : g = foldFn k h) (x : V) (hx : x ∈ lowSet g k)
    (hfree : ∀ y : lowSet g k, y.1 ∈ R → ¬ (Γ.induce (lowSet g k)).Reachable ⟨x, hx⟩ y) :
    reflectOn k g (liftSet Γ R k g h) x = h x := by
  subst hg
  by_cases hlt : k < h x
  · have hmem : x ∈ liftSet Γ R k (foldFn k h) h := ⟨hx, hlt, hfree⟩
    rw [reflectOn_pos hmem]
    show 2 * k - fold k (h x) = h x
    rw [fold_of_ge hlt.le]
    ring
  · have hmem : x ∉ liftSet Γ R k (foldFn k h) h := by
      rintro ⟨-, h1, -⟩
      exact hlt h1
    rw [reflectOn_neg hmem]
    show fold k (h x) = h x
    exact fold_of_le (not_lt.mp hlt)

theorem foldLift_injOn (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) :
    Set.InjOn (foldLift Γ R k) (Ext Γ R ρ) := by
  intro h1 hh1 h2 hh2 heq
  have hg : foldFn k h2 = foldFn k h1 := by
    rw [← foldFn_foldLift hh2.1 R k, ← heq, foldFn_foldLift hh1.1 R k]
  have hgx : ∀ x, fold k (h2 x) = fold k (h1 x) := fun x => congrFun hg x
  unfold foldLift at heq
  rw [hg] at heq
  funext x
  by_cases hx : x ∈ lowSet (foldFn k h1) k
  · by_cases hfree : ∀ y : lowSet (foldFn k h1) k, y.1 ∈ R →
        ¬ (Γ.induce (lowSet (foldFn k h1) k)).Reachable ⟨x, hx⟩ y
    · have e1 := reflectOn_liftSet_eq R k (foldFn k h1) h1 rfl x hx hfree
      have e2 := reflectOn_liftSet_eq R k (foldFn k h1) h2 hg.symm x hx hfree
      rw [← e1, ← e2, heq]
    · push Not at hfree
      obtain ⟨y, hyR, hreach⟩ := hfree
      have hS1 : ∀ z ∈ lowSet (foldFn k h1) k, h1 z ≠ k :=
        fun z hz => ne_of_fold_lt (show fold k (h1 z) < k from hz)
      have hS2 : ∀ z ∈ lowSet (foldFn k h1) k, h2 z ≠ k := by
        intro z hz
        have hz' : fold k (h1 z) < k := hz
        rw [← hgx z] at hz'
        exact ne_of_fold_lt hz'
      have s1 := sign_const hh1.1 (lowSet (foldFn k h1) k) hS1 ⟨x, hx⟩ y hreach
      have s2 := sign_const hh2.1 (lowSet (foldFn k h1) k) hS2 ⟨x, hx⟩ y hreach
      have hy : h1 y.1 = h2 y.1 := (hh1.2 _ hyR).trans (hh2.2 _ hyR).symm
      have n1 := hS1 x hx
      have n2 := hS2 x hx
      have e := hgx x
      have s1' : h1 x < k ↔ h1 y.1 < k := s1
      have s2' : h2 x < k ↔ h2 y.1 < k := s2
      rw [← hy] at s2'
      by_cases c : h1 x < k
      · have c2 : h2 x < k := s2'.mpr (s1'.mp c)
        rw [fold_of_le c.le, fold_of_le c2.le] at e
        exact e.symm
      · have c2 : ¬ h2 x < k := fun hc => c (s1'.mpr (s2'.mp hc))
        rw [fold_of_ge (by omega), fold_of_ge (by omega)] at e
        omega
  · have hx1 : ¬ fold k (h1 x) < k := hx
    have e := hgx x
    have a1 : fold k (h1 x) = k := le_antisymm (fold_le _ _) (not_lt.mp hx1)
    have a2 : fold k (h2 x) = k := e.trans a1
    have b1 : h1 x = k := by
      rcases le_total (h1 x) k with c | c
      · rw [fold_of_le c] at a1; exact a1
      · rw [fold_of_ge c] at a1; omega
    have b2 : h2 x = k := by
      rcases le_total (h2 x) k with c | c
      · rw [fold_of_le c] at a2; exact a2
      · rw [fold_of_ge c] at a2; omega
    rw [b1, b2]

/-- **A4 (Theorem 3.2, folding inequality).** `f ρ ≤ f (F_k ∘ ρ)`. -/
theorem fold_inequality [Finite V] (Γ : SimpleGraph V) (R : Set V)
    (hR : ∀ x : V, ∃ y ∈ R, Γ.Reachable x y) (ρ : V → ℤ) (k : ℤ) :
    numExt Γ R ρ ≤ numExt Γ R (foldFn k ρ) :=
  Set.ncard_le_ncard_of_injOn (foldLift Γ R k) (fun _ hh => foldLift_mem k hh)
    (foldLift_injOn Γ R ρ k) (ext_finite Γ R hR _)

/-! ### The fibre formulas -/

/-- The set `𝒢 = {g ∈ Ext (F_k ∘ ρ) | g ≤ k}`. -/
def foldTargets (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) : Set (V → ℤ) :=
  {g | g ∈ Ext Γ R (foldFn k ρ) ∧ ∀ x, g x ≤ k}

/-- `c g`: the number of connected components of `{g < k}` that contain no vertex of `R`. -/
noncomputable def freeComps (Γ : SimpleGraph V) (R : Set V) (k : ℤ) (g : V → ℤ) : ℕ :=
  Set.ncard {C : (Γ.induce (lowSet g k)).ConnectedComponent |
    ∀ x : lowSet g k, x.1 ∈ R → (Γ.induce (lowSet g k)).connectedComponentMk x ≠ C}

/-- `g` is admissible for `ρ`: no component of `{g < k}` contains a vertex of `R` with `ρ < k`
and a vertex of `R` with `ρ > k`. -/
def Admissible (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) (g : V → ℤ) : Prop :=
  ∀ y y' : lowSet g k, y.1 ∈ R → y'.1 ∈ R → ρ y.1 < k → k < ρ y'.1 →
    ¬ (Γ.induce (lowSet g k)).Reachable y y'

/-- **A5 (Theorem 3.2), first fibre formula.** -/
theorem fibre_formula_fold [Finite V] (Γ : SimpleGraph V) (R : Set V)
    (hR : ∀ x : V, ∃ y ∈ R, Γ.Reachable x y) (ρ : V → ℤ) (k : ℤ) :
    numExt Γ R (foldFn k ρ) = ∑ᶠ g ∈ foldTargets Γ R ρ k, 2 ^ freeComps Γ R k g := by
  sorry

/-- **A5 (Theorem 3.2), second fibre formula.** -/
theorem fibre_formula [Finite V] (Γ : SimpleGraph V) (R : Set V)
    (hR : ∀ x : V, ∃ y ∈ R, Γ.Reachable x y) (ρ : V → ℤ) (k : ℤ) :
    numExt Γ R ρ =
      ∑ᶠ g ∈ {g | g ∈ foldTargets Γ R ρ k ∧ Admissible Γ R ρ k g}, 2 ^ freeComps Γ R k g := by
  sorry

/-- Theorem 3.2, last sentence: the folding inequality is strict as soon as one element of `𝒢`
is not admissible. This is what the main theorem uses. -/
theorem fold_inequality_strict [Finite V] (Γ : SimpleGraph V) (R : Set V)
    (hR : ∀ x : V, ∃ y ∈ R, Γ.Reachable x y) (ρ : V → ℤ) (k : ℤ)
    (g : V → ℤ) (hg : g ∈ foldTargets Γ R ρ k) (hna : ¬ Admissible Γ R ρ k g) :
    numExt Γ R ρ < numExt Γ R (foldFn k ρ) := by
  have hnot : g ∉ foldLift Γ R k '' Ext Γ R ρ := by
    rintro ⟨h, hh, hEq⟩
    have hf : foldFn k h = g := by
      have e := foldFn_foldLift hh.1 R k
      rw [hEq] at e
      exact e.symm.trans (funext fun x => fold_of_le (hg.2 x))
    have hS : ∀ z ∈ lowSet g k, h z ≠ k := by
      intro z hz
      have hz' : g z < k := hz
      rw [← hf] at hz'
      exact ne_of_fold_lt hz'
    unfold Admissible at hna
    push Not at hna
    obtain ⟨y, y', hyR, hy'R, hlt, hgt, hreach⟩ := hna
    have s := sign_const hh.1 (lowSet g k) hS y y' hreach
    rw [hh.2 _ hyR, hh.2 _ hy'R] at s
    have := s.mp hlt
    omega
  have hss : foldLift Γ R k '' Ext Γ R ρ ⊂ Ext Γ R (foldFn k ρ) := by
    refine ⟨?_, fun hsub => hnot (hsub hg.1)⟩
    rintro _ ⟨h, hh, rfl⟩
    exact foldLift_mem k hh
  have hlt := Set.ncard_lt_ncard hss (ext_finite Γ R hR _)
  rw [(foldLift_injOn Γ R ρ k).ncard_image] at hlt
  exact hlt

end Max32
