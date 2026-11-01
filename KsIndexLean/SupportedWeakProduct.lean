module

public import KsIndexLean.WeakSmoothProduct

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace

/-- Outside the coefficient's topological support, the product and product jet are weakly zero. -/
lemma weakF_smooth_product_off_support (χ : ℂ → ℝ) (u : ℂ → ℂ)
    (U : ℂ → ℂ →L[ℝ] ℂ) :
    TauCeti.HasWeakFDerivOn volume
      (⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl⟩ : Opens ℂ)
      (fun z => χ z • u z) (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) := by
  have h0 : TauCeti.HasWeakFDerivOn volume
      (⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl⟩ : Opens ℂ)
      (0 : ℂ → ℂ) 0 :=
    TauCeti.hasWeakFDerivOn_zero
  apply (h0.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem (isClosed_tsupport χ).isOpen_compl.measurableSet] with z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  · filter_upwards [ae_restrict_mem (isClosed_tsupport χ).isOpen_compl.measurableSet] with z hz
    simp [image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz]

/-- Extend a supported product using genuine zero neighborhoods, with integrability explicit. -/
theorem weakF_smooth_mul_supported {Ω Λ : Opens ℂ} (hΩ : Ω ≤ Λ) {χ : ℂ → ℝ}
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Λ)
    (hs : (Λ : Set ℂ) ∩ tsupport χ ⊆ (Ω : Set ℂ))
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U)
    (hv : LocallyIntegrableOn (fun z => χ z • u z) Λ volume)
    (hJ : ∀ d, LocallyIntegrableOn
      (fun z => (χ z • U z + (fderiv ℝ χ z).smulRight (u z)) d) Λ volume) :
    TauCeti.HasWeakFDerivOn volume Λ (fun z => χ z • u z)
      (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) := by
  apply weakF_of_local hv hJ
  intro z hz
  by_cases h : z ∈ Ω
  · exact ⟨Ω, h, weakF_smooth_mul (hχ.mono hΩ) hw⟩
  · have hn : z ∉ tsupport χ := fun hmem => h (hs ⟨hz, hmem⟩)
    exact ⟨⟨(tsupport χ)ᶜ, (isClosed_tsupport χ).isOpen_compl⟩, hn,
      weakF_smooth_product_off_support χ u U⟩

/-- Annular L² value and operator-jet bounds discharge the extension integrability hypotheses. -/
theorem weakF_smooth_mul_supported_annulus {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {Ω : Opens ℂ} (hΩ : Ω ≤ annulusOpens a b) {χ : ℂ → ℝ}
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ (annulusOpens a b))
    (hs : annulusSet a b ∩ tsupport χ ⊆ (Ω : Set ℂ))
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U)
    (hv : MemLp (fun z => χ z • u z) 2 (volume.restrict (annulusSet a b)))
    (hJ : MemLp (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) 2
      (volume.restrict (annulusSet a b))) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens a b) (fun z => χ z • u z)
      (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) := by
  apply weakF_smooth_mul_supported hΩ hχ hs hw
  · exact (integrableOn_annulus_of_memLp ha hab hv).locallyIntegrableOn
  · intro d
    exact (integrableOn_annulus_of_memLp ha hab
      (hJ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ d))).locallyIntegrableOn

end KsIndex.Trace
