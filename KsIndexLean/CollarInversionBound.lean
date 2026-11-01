module

public import KsIndexLean.SphericalInversionMeasure
public import KsIndexLean.PolarPullback

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.Spherical

lemma sigma_mem_symmetric_collar {z : ℂ} (hz : z ∈ annulusSet (1 / 2 : ℝ) 2) :
    σ z ∈ annulusSet (1 / 2 : ℝ) 2 := by
  rw [mem_annulusSet, norm_σ]
  have hn : 0 < ‖z‖ := lt_trans (by norm_num) hz.1
  constructor
  · apply (lt_inv_comm₀ (by norm_num : (0 : ℝ) < 1 / 2) hn).mpr
    simpa using hz.2
  · apply (inv_lt_comm₀ hn (by norm_num : (0 : ℝ) < 2)).mpr
    simpa using hz.1

lemma sigma_image_symmetric_collar :
    σ '' annulusSet (1 / 2 : ℝ) 2 = annulusSet (1 / 2 : ℝ) 2 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact sigma_mem_symmetric_collar hw
  · intro hz
    exact ⟨σ z, sigma_mem_symmetric_collar hz, σ_σ z⟩

lemma sigma_collar_jacobian_le {z : ℂ} (hz : z ∈ annulusSet (1 / 2 : ℝ) 2) :
    |(fderiv ℝ σ z).toLinearMap.det| ≤ 16 := by
  have hn : 0 < ‖z‖ := lt_trans (by norm_num) hz.1
  rw [abs_det_sigma (norm_pos_iff.mp hn)]
  have hi : ‖z‖⁻¹ ≤ 2 := by
    simpa only [norm_σ] using (sigma_mem_symmetric_collar hz).2.le
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hn.le) hi 4
  norm_num at hp ⊢
  exact hp

/-- Inversion has a quantitative integral bound on the symmetric collar. -/
theorem lintegral_sigma_collar_le (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in annulusSet (1 / 2 : ℝ) 2, F (σ z) ∂volume) ≤
      16 * ∫⁻ z in annulusSet (1 / 2 : ℝ) 2, F z ∂volume := by
  have hd : ∀ z ∈ annulusSet (1 / 2 : ℝ) 2,
      HasFDerivWithinAt σ (fderiv ℝ σ z) (annulusSet (1 / 2 : ℝ) 2) z := by
    intro z hz
    have hn : z ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hz.1)
    exact (KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hn).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    measurableSet_annulusSet hd (Function.LeftInverse.injective σ_σ).injOn
    (fun z => F (σ z))
  rw [sigma_image_symmetric_collar] at hh
  simp only [σ_σ] at hh
  rw [hh, ← lintegral_const_mul _ hF]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact mul_le_mul_left (by exact_mod_cast sigma_collar_jacobian_le hz) (F z)

end KsIndex.Trace
