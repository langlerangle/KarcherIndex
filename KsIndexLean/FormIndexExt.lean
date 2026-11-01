module

/-
KsIndexLean — FormIndexExt: two small additions to the generic `FormIndex` engine.

1. `one_le_formIndex_of_neg`: a negative domain vector spans a negative line,
   so `formIndex ≥ 1` (the span-singleton argument of `Statements.ind_eq_one_iff`,
   made generic).
2. `formIndex_add_formNullity_add_one_le_card`: the **slice refinement** of the
   head-coordinate engine.  If `Q > 0` on the nonzero domain vectors vanishing on
   the head set `F`, AND `Q > 0` on the affine slice `{u ∈ D : u|_F = h}` for one
   head vector `h`, then `ind + nul + 1 ≤ |F|`.  Mechanism: a nonpositive
   subspace `W` injects into `F → ℂ` via the heads; if `dim W = |F|` the map is
   onto, so `W` contains a vector with heads `h`, contradicting nonpositivity.
   This is exactly the paper's `Zclasses` argument (the vector `w` with
   `ŵ(0) = 1/σ(0)`, `ŵ(−1) = −1/σ(−1)`).
-/
public import KsIndexLean.FormIndex

@[expose] public section


noncomputable section

namespace KsIndex.FormIndex

variable {ι : Type*}

/-- A negative domain vector gives `formIndex ≥ 1`. -/
theorem one_le_formIndex_of_neg {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)}
    (hsmul : ∀ (t : ℂ) (u : ι → ℂ), Q (t • u) = ‖t‖ ^ 2 * Q u)
    {u : ι → ℂ} (hu : u ∈ D) (hneg : Q u < 0) : 1 ≤ formIndex Q D := by
  have hune : u ≠ 0 := by
    rintro rfl
    have : Q (0 : ι → ℂ) = 0 := by
      have h := hsmul 0 0
      rw [zero_smul, norm_zero] at h
      simpa using h
    linarith
  have hVneg : NegOn Q D (ℂ ∙ u) := by
    refine ⟨(Submodule.span_singleton_le_iff_mem u D).mpr hu, ?_⟩
    intro w hw hwne
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have htne : t ≠ 0 := by
      rintro rfl
      exact hwne (zero_smul _ _)
    rw [hsmul]
    exact mul_neg_of_pos_of_neg (by positivity) hneg
  have hfd : FiniteDimensional ℂ ↥(ℂ ∙ u) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton u)
  have hfr : Module.finrank ℂ ↥(ℂ ∙ u) = 1 := finrank_span_singleton hune
  calc (1 : ℕ∞) = (Module.finrank ℂ ↥(ℂ ∙ u) : ℕ∞) := by simp [hfr]
    _ ≤ formIndex Q D :=
      le_iSup_of_le (ℂ ∙ u) (le_iSup_of_le hVneg (le_iSup_of_le hfd le_rfl))

/-- Slice refinement of `finrank_le_card_of_nonpos`: a nonpositive subspace has
dimension `< |F|` when `Q > 0` on an affine head slice. -/
lemma finrank_add_one_le_card_of_nonpos
    {Q : (ι → ℂ) → ℝ} {D : Submodule ℂ (ι → ℂ)} {F : Finset ι}
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u)
    (h : ↥F → ℂ) (hslice : ∀ u ∈ D, (∀ i : ↥F, u i = h i) → 0 < Q u)
    {W : Submodule ℂ (ι → ℂ)} [FiniteDimensional ℂ W]
    (hle : W ≤ D) (hW : ∀ u ∈ W, Q u ≤ 0) :
    Module.finrank ℂ W + 1 ≤ F.card := by
  classical
  set φ : ↥W →ₗ[ℂ] (↥F → ℂ) :=
    (LinearMap.pi fun i : ↥F => LinearMap.proj (i : ι)).comp W.subtype with hφ
  have hker : LinearMap.ker φ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hxne
    have hzero : φ x = 0 := LinearMap.mem_ker.mp hx
    have hcoord : ∀ i ∈ F, (x : ι → ℂ) i = 0 := by
      intro i hi
      have hj := congrFun hzero ⟨i, hi⟩
      simpa [hφ, LinearMap.pi_apply, LinearMap.proj_apply] using hj
    have hxc : (x : ι → ℂ) ≠ 0 := fun h => hxne (Submodule.coe_eq_zero.mp h)
    have hex : ∃ i, (x : ι → ℂ) i ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hxc
      exact ⟨i, by simpa using hi⟩
    have hpos' := hpos (x : ι → ℂ) (hle x.2) hcoord hex
    have hnp := hW (x : ι → ℂ) x.2
    linarith
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hker
  have hcard : Module.finrank ℂ (↥F → ℂ) = F.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  have hle' : Module.finrank ℂ W ≤ F.card := by
    calc Module.finrank ℂ W
        ≤ Module.finrank ℂ (↥F → ℂ) := LinearMap.finrank_le_finrank_of_injective hinj
      _ = F.card := hcard
  have hne : Module.finrank ℂ W ≠ F.card := by
    intro heq
    have hsurj : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hcard, heq])).mp hinj
    obtain ⟨w, hw⟩ := hsurj h
    have hheads : ∀ i : ↥F, (w : ι → ℂ) i = h i := by
      intro i
      have := congrFun hw i
      simpa [hφ, LinearMap.pi_apply, LinearMap.proj_apply] using this
    have hp := hslice (w : ι → ℂ) (hle w.2) hheads
    have hn := hW (w : ι → ℂ) w.2
    linarith
  omega

/-- Slice refinement at the finrank level (cf. `finrank_add_finrank_le_card`). -/
lemma finrank_add_finrank_add_one_le_card {Q : (ι → ℂ) → ℝ} {B : (ι → ℂ) → (ι → ℂ) → ℂ}
    {D V₁ V₂ : Submodule ℂ (ι → ℂ)} {F : Finset ι} (hQ0 : Q 0 = 0)
    (hBself : ∀ u : ι → ℂ, B u u = (Q u : ℂ))
    (hBaddL : ∀ {a b v : ι → ℂ}, a ∈ D → b ∈ D → v ∈ D →
      B (a + b) v = B a v + B b v)
    (hBaddR : ∀ {a v w : ι → ℂ}, a ∈ D → v ∈ D → w ∈ D →
      B a (v + w) = B a v + B a w)
    (hBconj : ∀ u v : ι → ℂ, B v u = (starRingEnd ℂ) (B u v))
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u)
    (h : ↥F → ℂ) (hslice : ∀ u ∈ D, (∀ i : ↥F, u i = h i) → 0 < Q u)
    (h₁ : NegOn Q D V₁) (h₂ : NullOn B D V₂)
    [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] :
    Module.finrank ℂ V₁ + Module.finrank ℂ V₂ + 1 ≤ F.card := by
  have hdisj : V₁ ⊓ V₂ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨hu₁, hu₂⟩ := Submodule.mem_inf.mp hu
    rw [Submodule.mem_bot]
    by_contra hne
    have hneg := h₁.2 u hu₁ hne
    have h0 : B u u = 0 := h₂.2 u hu₂ u (h₁.1 hu₁)
    have hcast : (Q u : ℂ) = 0 := by rw [← hBself, h0]
    have := Complex.ofReal_eq_zero.mp hcast
    linarith
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [hdisj, finrank_bot] at hsum
  have hW : Module.finrank ℂ ↥(V₁ ⊔ V₂) + 1 ≤ F.card :=
    finrank_add_one_le_card_of_nonpos hpos h hslice (sup_le h₁.1 h₂.1)
      (form_nonpos_on_sup hQ0 hBself hBaddL hBaddR hBconj h₁ h₂)
  omega

/-- **The slice-refined `ind + nul + 1 ≤ card F` theorem.** -/
theorem formIndex_add_formNullity_add_one_le_card {Q : (ι → ℂ) → ℝ}
    {B : (ι → ℂ) → (ι → ℂ) → ℂ} {D : Submodule ℂ (ι → ℂ)} {F : Finset ι}
    (hQ0 : Q 0 = 0) (hBself : ∀ u : ι → ℂ, B u u = (Q u : ℂ))
    (hBaddL : ∀ {a b v : ι → ℂ}, a ∈ D → b ∈ D → v ∈ D →
      B (a + b) v = B a v + B b v)
    (hBaddR : ∀ {a v w : ι → ℂ}, a ∈ D → v ∈ D → w ∈ D →
      B a (v + w) = B a v + B a w)
    (hBconj : ∀ u v : ι → ℂ, B v u = (starRingEnd ℂ) (B u v))
    (hpos : ∀ u ∈ D, (∀ i ∈ F, u i = 0) → (∃ i, u i ≠ 0) → 0 < Q u)
    (h : ↥F → ℂ) (hslice : ∀ u ∈ D, (∀ i : ↥F, u i = h i) → 0 < Q u) :
    formIndex Q D + formNullity B D + 1 ≤ F.card := by
  have hbot_neg : NegOn Q D ⊥ :=
    ⟨bot_le, fun u hu hune => absurd ((Submodule.mem_bot ℂ).mp hu) hune⟩
  have hbot_null : NullOn B D ⊥ := by
    refine ⟨bot_le, fun u hu v hv => ?_⟩
    rw [(Submodule.mem_bot ℂ).mp hu]
    have h := hBaddL D.zero_mem D.zero_mem hv
    rw [add_zero] at h
    linear_combination -h
  -- `ind + nul ≤ card F − 1` as a biSup bound, then shift by one
  have key : formIndex Q D + formNullity B D ≤ ((F.card - 1 : ℕ) : ℕ∞) := by
    rw [formIndex_eq_biSup, formNullity_eq_biSup]
    refine ENat.biSup_add_biSup_le'
      ⟨⊥, hbot_neg, inferInstance⟩ ⟨⊥, hbot_null, inferInstance⟩ ?_
    rintro V₁ ⟨hV₁, hfd₁⟩ V₂ ⟨hV₂, hfd₂⟩
    have := hfd₁
    have := hfd₂
    have hr := finrank_add_finrank_add_one_le_card hQ0 hBself hBaddL hBaddR hBconj hpos h
      hslice hV₁ hV₂
    exact_mod_cast (show Module.finrank ℂ V₁ + Module.finrank ℂ V₂ ≤ F.card - 1 by omega)
  have hFpos : 1 ≤ F.card := by
    by_contra hlt
    push Not at hlt
    have hF0 : F = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hF0
    have := hslice 0 D.zero_mem (fun i => (Finset.notMem_empty _ i.2).elim)
    linarith
  calc formIndex Q D + formNullity B D + 1
      ≤ ((F.card - 1 : ℕ) : ℕ∞) + 1 := by gcongr
    _ = F.card := by
      rw [← ENat.natCast_one, ← ENat.natCast_add]
      congr 1
      omega

end KsIndex.FormIndex
