module

public import KsIndexLean.SphericalInversionJacobian
public import KsIndexLean.EndChartSheets
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section


/-! Nonnegative energy transport through reflection in the unit circle.
An upper bound suffices for finiteness; no PDE is used. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart
open KsIndex.Spherical
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma opNorm_comp_sigma_le {z : ℂ} (hz : z ≠ 0) (L : ℂ →L[ℝ] F) :
    ‖L.comp (fderiv ℝ Bracket.σ z)‖ ≤ ‖z‖⁻¹ ^ 2 * ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [ContinuousLinearMap.comp_apply]
  change ‖L ((fderiv ℝ (fun w : ℂ => 1 / (starRingEnd ℂ) w) z) v)‖ ≤ _
  rw [SigmaDeriv.fderiv_sigmaR_apply hz]
  calc
    ‖L (-(((starRingEnd ℂ) z) ^ 2)⁻¹ * (starRingEnd ℂ) v)‖ ≤
        ‖L‖ * ‖-(((starRingEnd ℂ) z) ^ 2)⁻¹ * (starRingEnd ℂ) v‖ :=
      L.le_opNorm _
    _ = (‖z‖⁻¹ ^ 2 * ‖L‖) * ‖v‖ := by
      simp only [norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_conj]
      rw [inv_pow]
      ring

theorem lintegral_energy_comp_sigma_le {S : Set ℂ} (hS : MeasurableSet S)
    (h0 : ∀ z ∈ S, z ≠ 0) (Du : ℂ → (ℂ →L[ℝ] F)) :
    (∫⁻ z in S, ENNReal.ofReal
      (‖(Du (Bracket.σ z)).comp (fderiv ℝ Bracket.σ z)‖ ^ 2) ∂volume) ≤
    ∫⁻ w in Bracket.σ '' S, ENNReal.ofReal (‖Du w‖ ^ 2) ∂volume := by
  have hd : ∀ z ∈ S, HasFDerivWithinAt Bracket.σ (fderiv ℝ Bracket.σ z) S z :=
    fun z hz => (SigmaDeriv.hasFDerivAt_sigmaR (h0 z hz)).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hi : Set.InjOn Bracket.σ S := by
    intro x hx y hy h
    rw [← Bracket.σ_σ x, h, Bracket.σ_σ]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hd hi]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hS] with z hz
  rw [abs_det_sigma (h0 z hz), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    ‖(Du (Bracket.σ z)).comp (fderiv ℝ Bracket.σ z)‖ ^ 2 ≤
        (‖z‖⁻¹ ^ 2 * ‖Du (Bracket.σ z)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (opNorm_comp_sigma_le (h0 z hz) _) 2
    _ = ‖z‖⁻¹ ^ 4 * ‖Du (Bracket.σ z)‖ ^ 2 := by ring

/-- Energy of the reflected m-sheet pullback is bounded by m times the
base energy over the reflected image. -/
theorem lintegral_energy_reflected_endChart_le (p : ℂ) {m : ℕ} (hm : 0 < m)
    {A N : Set ℂ} (hA : MeasurableSet A) (hN : MeasurableSet N)
    (hAN : endChart p m '' A ⊆ N) (h0 : ∀ w ∈ N, w ≠ 0)
    (Du : ℂ → (ℂ →L[ℝ] F)) :
    (∫⁻ z in A, ENNReal.ofReal
      (‖((Du (Bracket.σ (endChart p m z))).comp
        (fderiv ℝ Bracket.σ (endChart p m z))).comp (endDeriv m z)‖ ^ 2) ∂volume) ≤
    (m : ℝ≥0∞) * ∫⁻ w in Bracket.σ '' N, ENNReal.ofReal (‖Du w‖ ^ 2) ∂volume :=
  (lintegral_energy_comp_endChart_le p hm hA hAN
    (fun w => (Du (Bracket.σ w)).comp (fderiv ℝ Bracket.σ w))).trans
      (mul_le_mul le_rfl (lintegral_energy_comp_sigma_le hN h0 Du) bot_le bot_le)

end KsIndex.EndChart
