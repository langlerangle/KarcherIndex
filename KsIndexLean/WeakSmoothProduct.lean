module

public import KsIndexLean.SmoothMultiplierTest

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

noncomputable section
namespace KsIndex.Trace

/-- Real smooth multiplication preserves the genuine weak directional derivative. -/
theorem weakLine_smooth_mul {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Ω) {u g : ℂ → ℂ} (d : ℂ)
    (hw : TauCeti.HasWeakLineDerivOn volume Ω u g d) :
    TauCeti.HasWeakLineDerivOn volume Ω (fun z => χ z • u z)
      (fun z => χ z • g z + (fderiv ℝ χ z d) • u z) d := by
  have hd : ContinuousOn (fun z => fderiv ℝ χ z d) (Ω : Set ℂ) :=
    (hχ.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hu := LocallyIntegrableOn.continuousOn_smul Ω.isOpen.isLocallyClosed
    hw.locallyIntegrableOn hχ.continuousOn
  have hg := LocallyIntegrableOn.continuousOn_smul Ω.isOpen.isLocallyClosed
    hw.locallyIntegrableOn_deriv hχ.continuousOn
  have hdU := LocallyIntegrableOn.continuousOn_smul Ω.isOpen.isLocallyClosed
    hw.locallyIntegrableOn hd
  rw [TauCeti.hasWeakLineDerivOn_iff_testFunction]
  refine ⟨inferInstance, hu, hg.add hdU, ?_⟩
  intro φ
  have hA := TauCeti.integrable_smul_of_locallyIntegrableOn hdU φ
  have hB := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn hu φ d
  have hC := TauCeti.integrable_smul_of_locallyIntegrableOn hg φ
  have he := hw.integral_lineDeriv_smul_eq_neg_integral_smul (smoothMultiplierTest χ hχ φ)
  have he' : (∫ z, φ z • ((fderiv ℝ χ z d) • u z)) +
      (∫ z, lineDeriv ℝ (φ : ℂ → ℝ) z d • (χ z • u z)) =
      -(∫ z, φ z • (χ z • g z)) := by
    convert he using 1
    · rw [← integral_add hA hB]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change φ z • ((fderiv ℝ χ z d) • u z) +
          lineDeriv ℝ (φ : ℂ → ℝ) z d • (χ z • u z) =
          lineDeriv ℝ (smoothMultiplierTest χ hχ φ : ℂ → ℝ) z d • u z
        rw [lineDeriv_smoothMultiplierTest]
        simp only [add_smul, smul_smul]
        module
    · congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change φ z • (χ z • g z) = (χ z * φ z) • g z
        rw [smul_smul, mul_comm]
  simp only [smul_add]
  rw [integral_add hC hA]
  linear_combination he'

/-- The full weak Fréchet product rule, with smoothness required only on the domain. -/
theorem weakF_smooth_mul {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiffOn ℝ (⊤ : ℕ∞) χ Ω) {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U) :
    TauCeti.HasWeakFDerivOn volume Ω (fun z => χ z • u z)
      (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) := by
  rw [TauCeti.hasWeakFDerivOn_iff]
  intro d
  simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply] using
    weakLine_smooth_mul hχ d (hw.hasWeakLineDerivOn d)

end KsIndex.Trace
