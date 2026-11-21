/-
The folding injection.
Paper: gasm_32_11 (and gasm_32_10), Section 3, Corollary 3.3.

For `h ∈ Ext ρ` the paper defines `Φ_k h = 2k - h` on the connected components of `{h > k}` that
contain a ring vertex, and `Φ_k h = h` elsewhere. Here this is `phi Γ R k h`.

Proved in this file, for an arbitrary graph `Γ` and an arbitrary set `R` of its vertices:

* `phi_eq_foldLift`  `Φ_k` is the map `foldLift` of `Fold.lean` (which was defined through the
                      components of `{F_k h < k}`);
* `phi_mem`          `Φ_k` maps `Ext ρ` into `Ext (F_k ∘ ρ)`;
* `foldFn_phi`       `F_k (Φ_k h) = F_k h`;
* `phi_injOn`        `Φ_k` is injective on `Ext ρ`;
* `phi_image`        `h' ∈ Ext (F_k ∘ ρ)` is in the image of `Φ_k` iff `F_k h'` is admissible for `ρ`;
* `phi_surjOn_iff`   `Φ_k` is onto iff every `g ∈ 𝒢` is admissible;
* `phi_bijOn_iff`    `Φ_k` is a bijection iff `f ρ = f (F_k ∘ ρ)` (when `Ext` is finite).

No `sorry`.
-/
import Max32Lean.Fold

namespace Max32

variable {V : Type*}

/-- The set `{x | k < h x}`. -/
def highSet (h : V → ℤ) (k : ℤ) : Set V := {x | k < h x}

theorem highSet_subset_lowSet (k : ℤ) (h : V → ℤ) : highSet h k ⊆ lowSet (foldFn k h) k := by
  intro x hx
  have hx' : k < h x := hx
  show fold k (h x) < k
  rw [fold_of_ge hx'.le]
  omega

/-- A path inside `{h > k}` is a path inside `{F_k h < k}`. -/
theorem reach_low_of_high {Γ : SimpleGraph V} (k : ℤ) (h : V → ℤ) (x y : highSet h k)
    (hxy : (Γ.induce (highSet h k)).Reachable x y) :
    (Γ.induce (lowSet (foldFn k h) k)).Reachable
      ⟨x.1, highSet_subset_lowSet k h x.2⟩ ⟨y.1, highSet_subset_lowSet k h y.2⟩ := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj _ ih =>
    have hadj' : Γ.Adj u.1 v.1 := hadj
    have a : (Γ.induce (lowSet (foldFn k h) k)).Adj
        ⟨u.1, highSet_subset_lowSet k h u.2⟩ ⟨v.1, highSet_subset_lowSet k h v.2⟩ := hadj'
    exact a.reachable.trans ih

/-- A path inside `{F_k h < k}` that starts at a vertex with `h > k` stays inside `{h > k}`. -/
theorem reach_high_of_low {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (k : ℤ)
    (x y : lowSet (foldFn k h) k)
    (hxy : (Γ.induce (lowSet (foldFn k h) k)).Reachable x y) (hx : k < h x.1) :
    ∃ hy : k < h y.1, (Γ.induce (highSet h k)).Reachable ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact ⟨hx, SimpleGraph.Reachable.refl _⟩
  | @cons u v w hadj _ ih =>
    have hadj' : Γ.Adj u.1 v.1 := hadj
    have h1 := (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp (hh _ _ hadj')
    have hv : h v.1 ≠ k := ne_of_fold_lt (show fold k (h v.1) < k from v.2)
    have hvk : k < h v.1 := by omega
    obtain ⟨hw, r⟩ := ih hvk
    have a : (Γ.induce (highSet h k)).Adj ⟨u.1, hx⟩ ⟨v.1, hvk⟩ := hadj'
    exact ⟨hw, a.reachable.trans r⟩

/-- The vertices of the connected components of `{h > k}` that contain a vertex of `R`. -/
def touchSet (Γ : SimpleGraph V) (R : Set V) (k : ℤ) (h : V → ℤ) : Set V :=
  {x | ∃ hx : x ∈ highSet h k, ∃ y : highSet h k,
    y.1 ∈ R ∧ (Γ.induce (highSet h k)).Reachable ⟨x, hx⟩ y}

/-- **The folding injection `Φ_k` of Corollary 3.3**: `2k - h` on the components of `{h > k}` that
contain a vertex of `R`, and `h` elsewhere. -/
noncomputable def phi (Γ : SimpleGraph V) (R : Set V) (k : ℤ) (h : V → ℤ) : V → ℤ :=
  reflectOn k h (touchSet Γ R k h)

/-- `Φ_k` is the map `foldLift` of `Fold.lean`. -/
theorem phi_eq_foldLift {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (R : Set V) (k : ℤ) :
    phi Γ R k h = foldLift Γ R k h := by
  funext x
  show reflectOn k h (touchSet Γ R k h) x =
    reflectOn k (foldFn k h) (liftSet Γ R k (foldFn k h) h) x
  by_cases hx : k < h x
  · have hxl : x ∈ lowSet (foldFn k h) k := highSet_subset_lowSet k h hx
    by_cases ht : x ∈ touchSet Γ R k h
    · have hnl : x ∉ liftSet Γ R k (foldFn k h) h := by
        rintro ⟨hx', -, hfree⟩
        obtain ⟨hx'', y, hyR, hreach⟩ := ht
        exact hfree ⟨y.1, highSet_subset_lowSet k h y.2⟩ hyR
          (reach_low_of_high k h ⟨x, hx''⟩ y hreach)
      rw [reflectOn_pos ht, reflectOn_neg hnl]
      show 2 * k - h x = fold k (h x)
      rw [fold_of_ge hx.le]
    · have hl : x ∈ liftSet Γ R k (foldFn k h) h := by
        refine ⟨hxl, hx, ?_⟩
        intro y hyR hreach
        obtain ⟨hy, r⟩ := reach_high_of_low hh k ⟨x, hxl⟩ y hreach hx
        exact ht ⟨hx, ⟨y.1, hy⟩, hyR, r⟩
      rw [reflectOn_neg ht, reflectOn_pos hl]
      show h x = 2 * k - fold k (h x)
      rw [fold_of_ge hx.le]
      ring
  · have ht : x ∉ touchSet Γ R k h := by
      rintro ⟨hx', -⟩
      exact hx hx'
    have hnl : x ∉ liftSet Γ R k (foldFn k h) h := by
      rintro ⟨-, h1, -⟩
      exact hx h1
    rw [reflectOn_neg ht, reflectOn_neg hnl]
    show h x = fold k (h x)
    rw [fold_of_le (not_lt.mp hx)]

/-- **Corollary 3.3.** `Φ_k` maps `Ext ρ` into `Ext (F_k ∘ ρ)`. -/
theorem phi_mem {Γ : SimpleGraph V} {R : Set V} {ρ h : V → ℤ} (k : ℤ)
    (hh : h ∈ Ext Γ R ρ) : phi Γ R k h ∈ Ext Γ R (foldFn k ρ) := by
  rw [phi_eq_foldLift hh.1 R k]
  exact foldLift_mem k hh

/-- **Corollary 3.3.** `F_k (Φ_k h) = F_k h`. -/
theorem foldFn_phi {Γ : SimpleGraph V} {h : V → ℤ} (hh : IsHeight Γ h) (R : Set V) (k : ℤ) :
    foldFn k (phi Γ R k h) = foldFn k h := by
  rw [phi_eq_foldLift hh R k]
  exact foldFn_foldLift hh R k

/-- **Corollary 3.3.** `Φ_k` is injective on `Ext ρ`. -/
theorem phi_injOn (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) :
    Set.InjOn (phi Γ R k) (Ext Γ R ρ) := by
  intro h1 hh1 h2 hh2 heq
  rw [phi_eq_foldLift hh1.1 R k, phi_eq_foldLift hh2.1 R k] at heq
  exact foldLift_injOn Γ R ρ k hh1 hh2 heq

/-! ### The image of `Φ_k` -/

theorem eq_of_fold_eq {k a : ℤ} (h : fold k a = k) : a = k := by
  rcases le_total a k with c | c
  · rw [fold_of_le c] at h
    exact h
  · rw [fold_of_ge c] at h
    omega

/-- The fold of an element of `Ext (F_k ∘ ρ)` lies in `𝒢`. -/
theorem foldFn_mem_foldTargets {Γ : SimpleGraph V} {R : Set V} {ρ h' : V → ℤ} (k : ℤ)
    (hh : h' ∈ Ext Γ R (foldFn k ρ)) : foldFn k h' ∈ foldTargets Γ R ρ k := by
  refine ⟨⟨isHeight_fold hh.1 k, fun x hx => ?_⟩, foldFn_le k h'⟩
  show fold k (h' x) = fold k (ρ x)
  rw [hh.2 x hx]
  exact fold_fold_le k (ρ x)

/-- The fold of an element of `Ext ρ` is admissible for `ρ`. -/
theorem admissible_foldFn {Γ : SimpleGraph V} {R : Set V} {ρ h : V → ℤ} (k : ℤ)
    (hh : h ∈ Ext Γ R ρ) : Admissible Γ R ρ k (foldFn k h) := by
  intro y y' hyR hy'R hlt hgt hreach
  have hS : ∀ z ∈ lowSet (foldFn k h) k, h z ≠ k :=
    fun z hz => ne_of_fold_lt (show fold k (h z) < k from hz)
  have s := sign_const hh.1 (lowSet (foldFn k h) k) hS y y' hreach
  rw [hh.2 _ hyR, hh.2 _ hy'R] at s
  have := s.mp hlt
  omega

/-- The components of `{g < k}` that have to be reflected to get the preimage of `h'` under `Φ_k`:
those that contain a vertex of `R` with `ρ > k`, and those without a vertex of `R` on which
`h' > k`. -/
def unliftSet (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) (g h' : V → ℤ) : Set V :=
  {x | ∃ hx : x ∈ lowSet g k,
    (∃ y : lowSet g k, y.1 ∈ R ∧ k < ρ y.1 ∧ (Γ.induce (lowSet g k)).Reachable ⟨x, hx⟩ y) ∨
    (k < h' x ∧ ∀ y : lowSet g k, y.1 ∈ R → ¬ (Γ.induce (lowSet g k)).Reachable ⟨x, hx⟩ y)}

/-- If `H` folds to `F_k h'` and agrees with `h'` on the components of `{F_k h' < k}` without a
vertex of `R`, then `foldLift H = h'`. -/
theorem foldLift_eq_of {Γ : SimpleGraph V} {R : Set V} {ρ h' : V → ℤ} (k : ℤ)
    (hh' : h' ∈ Ext Γ R (foldFn k ρ)) (H : V → ℤ) (hF : foldFn k H = foldFn k h')
    (hval : ∀ x (hx : x ∈ lowSet (foldFn k h') k),
      (∀ y : lowSet (foldFn k h') k, y.1 ∈ R →
        ¬ (Γ.induce (lowSet (foldFn k h') k)).Reachable ⟨x, hx⟩ y) → H x = h' x) :
    foldLift Γ R k H = h' := by
  have hS : ∀ z ∈ lowSet (foldFn k h') k, h' z ≠ k :=
    fun z hz => ne_of_fold_lt (show fold k (h' z) < k from hz)
  unfold foldLift
  rw [hF]
  funext x
  by_cases hx : x ∈ lowSet (foldFn k h') k
  · by_cases hfree : ∀ y : lowSet (foldFn k h') k, y.1 ∈ R →
        ¬ (Γ.induce (lowSet (foldFn k h') k)).Reachable ⟨x, hx⟩ y
    · rw [reflectOn_liftSet_eq R k (foldFn k h') H hF.symm x hx hfree]
      exact hval x hx hfree
    · push Not at hfree
      obtain ⟨y, hyR, hreach⟩ := hfree
      have hnl : x ∉ liftSet Γ R k (foldFn k h') H := by
        rintro ⟨hx', -, hf⟩
        exact hf y hyR hreach
      rw [reflectOn_neg hnl]
      have s := sign_const hh'.1 (lowSet (foldFn k h') k) hS ⟨x, hx⟩ y hreach
      have hyle : h' y.1 ≤ k := by
        rw [hh'.2 _ hyR]
        exact fold_le k _
      have hyne := hS y.1 y.2
      have hxk : h' x < k := s.mpr (by omega)
      show fold k (h' x) = h' x
      exact fold_of_le hxk.le
  · have hnl : x ∉ liftSet Γ R k (foldFn k h') H := by
      rintro ⟨hx', -⟩
      exact hx hx'
    rw [reflectOn_neg hnl]
    have hx1 : ¬ fold k (h' x) < k := hx
    have a : fold k (h' x) = k := le_antisymm (fold_le _ _) (not_lt.mp hx1)
    show fold k (h' x) = h' x
    rw [a]
    exact (eq_of_fold_eq a).symm

/-- Every `h' ∈ Ext (F_k ∘ ρ)` whose fold is admissible for `ρ` is `Φ_k h` for some `h ∈ Ext ρ`. -/
theorem exists_preimage {Γ : SimpleGraph V} {R : Set V} {ρ h' : V → ℤ} (k : ℤ)
    (hh' : h' ∈ Ext Γ R (foldFn k ρ)) (hadm : Admissible Γ R ρ k (foldFn k h')) :
    ∃ h ∈ Ext Γ R ρ, phi Γ R k h = h' := by
  have hgH : IsHeight Γ (foldFn k h') := isHeight_fold hh'.1 k
  have hS : ∀ z ∈ lowSet (foldFn k h') k, h' z ≠ k :=
    fun z hz => ne_of_fold_lt (show fold k (h' z) < k from hz)
  have hgR : ∀ x ∈ R, foldFn k h' x = fold k (ρ x) := by
    intro x hx
    show fold k (h' x) = fold k (ρ x)
    rw [hh'.2 x hx]
    exact fold_fold_le k (ρ x)
  have hU : IsUnionOfComponents Γ (foldFn k h') k (unliftSet Γ R ρ k (foldFn k h') h') := by
    constructor
    · rintro x ⟨hx, -⟩
      exact hx
    · rintro x y hxy ⟨hx, hc⟩
      refine ⟨y.2, ?_⟩
      rcases hc with ⟨z, hzR, hz, hr⟩ | ⟨hlt, hfree⟩
      · exact Or.inl ⟨z, hzR, hz, hxy.symm.trans hr⟩
      · have s := sign_const hh'.1 (lowSet (foldFn k h') k) hS x y hxy
        have hy := hS y.1 y.2
        refine Or.inr ⟨?_, fun z hz hyz => hfree z hz (hxy.trans hyz)⟩
        by_contra hc
        have hyk : h' y.1 < k := by omega
        have hxk := s.mpr hyk
        omega
  obtain ⟨hH, hF⟩ := reflectOn_isHeight hgH k (foldFn_le k h') _ hU
  have hmem : reflectOn k (foldFn k h') (unliftSet Γ R ρ k (foldFn k h') h') ∈ Ext Γ R ρ := by
    refine ⟨hH, fun x hxR => ?_⟩
    by_cases hx : k < ρ x
    · have hxl : x ∈ lowSet (foldFn k h') k := by
        show foldFn k h' x < k
        rw [hgR x hxR, fold_of_ge hx.le]
        omega
      have hxT : x ∈ unliftSet Γ R ρ k (foldFn k h') h' :=
        ⟨hxl, Or.inl ⟨⟨x, hxl⟩, hxR, hx, SimpleGraph.Reachable.refl _⟩⟩
      rw [reflectOn_pos hxT, hgR x hxR, fold_of_ge hx.le]
      ring
    · have hxT : x ∉ unliftSet Γ R ρ k (foldFn k h') h' := by
        rintro ⟨hxl, hc⟩
        rcases hc with ⟨z, hzR, hz, hr⟩ | ⟨-, hfree⟩
        · have hxlt : ρ x < k := by
            have e : foldFn k h' x < k := hxl
            rw [hgR x hxR, fold_of_le (not_lt.mp hx)] at e
            exact e
          exact hadm ⟨x, hxl⟩ z hxR hzR hxlt hz hr
        · exact hfree ⟨x, hxl⟩ hxR (SimpleGraph.Reachable.refl _)
      rw [reflectOn_neg hxT, hgR x hxR, fold_of_le (not_lt.mp hx)]
  refine ⟨_, hmem, ?_⟩
  rw [phi_eq_foldLift hH R k]
  refine foldLift_eq_of k hh' _ hF ?_
  intro x hx hfree
  by_cases hlt : k < h' x
  · have hxT : x ∈ unliftSet Γ R ρ k (foldFn k h') h' := ⟨hx, Or.inr ⟨hlt, hfree⟩⟩
    rw [reflectOn_pos hxT]
    show 2 * k - fold k (h' x) = h' x
    rw [fold_of_ge hlt.le]
    ring
  · have hxT : x ∉ unliftSet Γ R ρ k (foldFn k h') h' := by
      rintro ⟨hx', hc⟩
      rcases hc with ⟨z, hzR, -, hr⟩ | ⟨h1, -⟩
      · exact hfree z hzR hr
      · exact hlt h1
    rw [reflectOn_neg hxT]
    show fold k (h' x) = h' x
    exact fold_of_le (not_lt.mp hlt)

/-- **Corollary 3.3.** A function `h' ∈ Ext (F_k ∘ ρ)` is in the image of `Φ_k` if and only if
`F_k h'` is admissible for `ρ`. -/
theorem phi_image (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) :
    phi Γ R k '' Ext Γ R ρ =
      {h' | h' ∈ Ext Γ R (foldFn k ρ) ∧ Admissible Γ R ρ k (foldFn k h')} := by
  ext h'
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨phi_mem k hh, ?_⟩
    rw [foldFn_phi hh.1 R k]
    exact admissible_foldFn k hh
  · rintro ⟨hh', hadm⟩
    obtain ⟨h, hh, e⟩ := exists_preimage k hh' hadm
    exact ⟨h, hh, e⟩

/-- `Φ_k` is onto `Ext (F_k ∘ ρ)` if and only if every `g ∈ 𝒢` is admissible for `ρ`. -/
theorem phi_surjOn_iff (Γ : SimpleGraph V) (R : Set V) (ρ : V → ℤ) (k : ℤ) :
    Set.SurjOn (phi Γ R k) (Ext Γ R ρ) (Ext Γ R (foldFn k ρ)) ↔
      ∀ g ∈ foldTargets Γ R ρ k, Admissible Γ R ρ k g := by
  constructor
  · intro hs g hg
    have hin : g ∈ phi Γ R k '' Ext Γ R ρ := hs hg.1
    rw [phi_image] at hin
    have e : foldFn k g = g := funext fun x => fold_of_le (hg.2 x)
    have a := hin.2
    rw [e] at a
    exact a
  · intro hall h' hh'
    rw [phi_image]
    exact ⟨hh', hall _ (foldFn_mem_foldTargets k hh')⟩

/-- **Corollary 3.3, last sentence.** `Φ_k` is a bijection from `Ext ρ` to `Ext (F_k ∘ ρ)` if and
only if `f ρ = f (F_k ∘ ρ)`. -/
theorem phi_bijOn_iff [Finite V] (Γ : SimpleGraph V) (R : Set V)
    (hR : ∀ x : V, ∃ y ∈ R, Γ.Reachable x y) (ρ : V → ℤ) (k : ℤ) :
    Set.BijOn (phi Γ R k) (Ext Γ R ρ) (Ext Γ R (foldFn k ρ)) ↔
      numExt Γ R ρ = numExt Γ R (foldFn k ρ) := by
  have hmaps : Set.MapsTo (phi Γ R k) (Ext Γ R ρ) (Ext Γ R (foldFn k ρ)) :=
    fun _ hh => phi_mem k hh
  have hinj := phi_injOn Γ R ρ k
  constructor
  · intro hb
    unfold numExt
    rw [← hb.image_eq, hinj.ncard_image]
  · intro he
    refine ⟨hmaps, hinj, ?_⟩
    have hsub : phi Γ R k '' Ext Γ R ρ ⊆ Ext Γ R (foldFn k ρ) := hmaps.image_subset
    have hcard : (Ext Γ R (foldFn k ρ)).ncard ≤ (phi Γ R k '' Ext Γ R ρ).ncard := by
      rw [hinj.ncard_image]
      exact he.ge
    have heq := Set.eq_of_subset_of_ncard_le hsub hcard (ext_finite Γ R hR _)
    intro y hy
    rw [← heq] at hy
    exact hy

end Max32
