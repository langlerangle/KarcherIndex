module

public import KsIndexLean.SphericalInversionJacobian

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

lemma sigma_image_nonzero : Bracket.σ '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [Bracket.σ] using hw
  · intro hz
    refine ⟨Bracket.σ z, ?_, Bracket.σ_σ z⟩
    simpa [Bracket.σ] using hz

/-- Genuine change of variables for the metric-weighted planar integral. -/
theorem lintegral_stereo_weight_sigma (F : ℂ → ℝ≥0∞) :
    ∫⁻ z, ENNReal.ofReal (stereoAreaDensity z) * F z ∂volume =
      ∫⁻ z, ENNReal.ofReal (stereoAreaDensity z) * F (Bracket.σ z) ∂volume := by
  have hd : ∀ z ∈ ({0}ᶜ : Set ℂ),
      HasFDerivWithinAt Bracket.σ (fderiv ℝ Bracket.σ z) ({0}ᶜ : Set ℂ) z := by
    intro z hz
    have hh := SigmaDeriv.hasFDerivAt_sigmaR (by simpa using hz)
    exact hh.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn Bracket.σ ({0}ᶜ : Set ℂ) :=
    (Function.LeftInverse.injective Bracket.σ_σ).injOn
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (measurableSet_singleton (0 : ℂ)).compl hd hinj
    (fun z => ENNReal.ofReal (stereoAreaDensity z) * F z)
  rw [sigma_image_nonzero] at h
  simp only [restrict_compl_singleton] at h
  refine h.trans ?_
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℂ)] with z hz
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), stereoAreaDensity_jacobian hz]

lemma measurable_sigma : Measurable Bracket.σ := by
  unfold Bracket.σ
  fun_prop

lemma lintegral_stereoAreaMeasure (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂stereoAreaMeasure =
      ∫⁻ z, ENNReal.ofReal (stereoAreaDensity z) * F z ∂volume := by
  exact lintegral_withDensity_eq_lintegral_mul volume
    continuous_stereoAreaDensity.measurable.ennreal_ofReal hF

lemma map_stereoAreaMeasure_sigma :
    Measure.map Bracket.σ stereoAreaMeasure = stereoAreaMeasure := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_sigma]
  have hc : Measurable (fun z => F (Bracket.σ z)) := hF.comp measurable_sigma
  rw [lintegral_stereoAreaMeasure _ hc, lintegral_stereoAreaMeasure F hF]
  exact (lintegral_stereo_weight_sigma F).symm

end KsIndex.Spherical
