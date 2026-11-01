module

public import KsIndexLean.CollarInversionLimit
public import KsIndexLean.WeakH1Adapter

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.WeakH1

lemma sigma_collar_derivative_bound {z : ℂ} (hz : z ∈ annulusSet (1 / 2 : ℝ) 2)
    (d : ℂ) : ‖fderiv ℝ σ z d‖ ≤ 4 * ‖d‖ := by
  have hn : 0 < ‖z‖ := lt_trans (by norm_num) hz.1
  change ‖fderiv ℝ (fun w : ℂ => 1 / (starRingEnd ℂ) w) z d‖ ≤ 4 * ‖d‖
  rw [KsIndex.SigmaDeriv.fderiv_sigmaR_apply (norm_pos_iff.mp hn)]
  simp only [norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_conj]
  have hi : ‖z‖⁻¹ ≤ 2 := by
    simpa only [norm_σ] using (sigma_mem_symmetric_collar hz).2.le
  have hp : ‖z‖⁻¹ ^ 2 ≤ 4 := by
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hn.le) hi 2
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
  rw [← inv_pow]
  exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)

lemma sigma_collar_derivative_re_bound (d : ℂ) :
    ∀ᵐ z ∂volume.restrict (annulusSet (1 / 2 : ℝ) 2),
      ‖(fderiv ℝ σ z d).re‖ ≤ 4 * ‖d‖ := by
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact (Complex.abs_re_le_norm _).trans (sigma_collar_derivative_bound hz d)

lemma sigma_collar_derivative_im_bound (d : ℂ) :
    ∀ᵐ z ∂volume.restrict (annulusSet (1 / 2 : ℝ) 2),
      ‖(fderiv ℝ σ z d).im‖ ≤ 4 * ‖d‖ := by
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact (Complex.abs_im_le_norm _).trans (sigma_collar_derivative_bound hz d)

/-- Coordinate form of the derivative pullback, for both smooth and weak jets. -/
def sigmaJetPullback (X Y : ℂ → ℂ) (d z : ℂ) : ℂ :=
  (fderiv ℝ σ z d).re • X (σ z) + (fderiv ℝ σ z d).im • Y (σ z)

lemma sigmaJetPullback_eq (J : ℂ → ℂ →L[ℝ] ℂ) (d z : ℂ) :
    sigmaJetPullback (fun w => J w 1) (fun w => J w Complex.I) d z =
      (J (σ z)).comp (fderiv ℝ σ z) d := by
  exact (realLinear_coordinates (J (σ z)) (fderiv ℝ σ z d)).symm

lemma fderiv_comp_sigma {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℝ f (σ z)) (d : ℂ) :
    fderiv ℝ (f ∘ σ) z d =
      sigmaJetPullback (fun w => fderiv ℝ f w 1) (fun w => fderiv ℝ f w Complex.I) d z := by
  rw [fderiv_comp z hf (KsIndex.SigmaDeriv.hasFDerivAt_sigmaR hz).differentiableAt]
  exact (sigmaJetPullback_eq (fderiv ℝ f) d z).symm

end KsIndex.Trace
