module

public import KsIndexLean.AngularFourierIdentity

@[expose] public section


/-! Finite Fourier energy estimates for weak disk profiles. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma circleFourier_finite_sq_le (f : Lp ℂ 2 circleMeasure) (F : Finset ℤ) :
    (∑ n ∈ F, ‖circleFourierCoeff f n‖ ^ 2) ≤ (2 * Real.pi)⁻¹ * ‖f‖ ^ 2 := by
  have h := hasSum_sq_circleFourierCoeff (Lp.memLp f)
  rw [integral_sq_norm_circleL2] at h
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum F (fun n _ => sq_nonneg _)

lemma norm_angular_coefficient_sq (n : ℤ) (a : ℂ) :
    ‖((n : ℂ) * Complex.I) * a‖ ^ 2 = (n : ℝ) ^ 2 * ‖a‖ ^ 2 := by
  simp [mul_pow]

/-- Bessel bounds for values and angular derivatives control the first-order
Sobolev squared weight `(1+|n|)²`, uniformly in the finite set of modes. -/
theorem circleFourier_finite_weight_sq_le (f g : Lp ℂ 2 circleMeasure)
    (h : ∀ n : ℤ, circleFourierCoeff g n = ((n : ℂ) * Complex.I) * circleFourierCoeff f n)
    (F : Finset ℤ) :
    (∑ n ∈ F, (1 + |(n : ℝ)|) ^ 2 * ‖circleFourierCoeff f n‖ ^ 2) ≤
      2 * (2 * Real.pi)⁻¹ * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have hp : ∀ n : ℤ, (1 + |(n : ℝ)|) ^ 2 * ‖circleFourierCoeff f n‖ ^ 2 ≤
      2 * (‖circleFourierCoeff f n‖ ^ 2 + ‖circleFourierCoeff g n‖ ^ 2) := by
    intro n
    rw [h n, norm_angular_coefficient_sq]
    have ha : (1 + |(n : ℝ)|) ^ 2 ≤ 2 * (1 + (n : ℝ) ^ 2) := by
      nlinarith [sq_nonneg (|(n : ℝ)| - 1), sq_abs (n : ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg ‖circleFourierCoeff f n‖)]
  have hsum := Finset.sum_le_sum (fun n (_ : n ∈ F) => hp n)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hf := circleFourier_finite_sq_le f F
  have hg := circleFourier_finite_sq_le g F
  nlinarith

/-- A single full-measure set supports all integer angular Fourier identities. -/
theorem disk_angular_fourier_all_ae (u : ComplexH1) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 1), ∀ n : ℤ,
      circleFourierCoeff (diskAngularProfile u r) n =
        ((n : ℂ) * Complex.I) * circleFourierCoeff (diskProfile u r) n :=
  ae_all_iff.mpr (disk_angular_fourier_ae u)

/-- Finite-mode weighted energy bound on the actual radial representative. -/
theorem diskMode_finite_weight_sq_le_ae (u : ComplexH1) (F : Finset ℤ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      (∑ n ∈ F, (1 + |(n : ℝ)|) ^ 2 * ‖diskMode u n r‖ ^ 2) ≤
        2 * (2 * Real.pi)⁻¹ * (‖diskProfile u r‖ ^ 2 + ‖diskAngularProfile u r‖ ^ 2) := by
  filter_upwards [disk_angular_fourier_all_ae u, diskRepresentative_ae u] with r hr he
  have hm : ∀ n, diskMode u n r = circleFourierCoeff (diskProfile u r) n := by
    intro n
    rw [diskMode, circleCoefficientCLM_apply, ← he]
  simp_rw [hm]
  exact circleFourier_finite_weight_sq_le _ _ hr F

lemma diskMode_sq_integrable (u : ComplexH1) (n : ℤ) :
    IntervalIntegrable (fun r => ‖diskMode u n r‖ ^ 2) volume (1 / 2) 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  exact (continuous_pow 2).comp_continuousOn (diskMode_continuousOn u n).norm

/-- The finite-mode bound is integrable on the collar, with its normalization retained. -/
theorem diskMode_integral_finite_weight_sq_le (u : ComplexH1) (F : Finset ℤ) :
    (∫ r in (1 / 2 : ℝ)..1, ∑ n ∈ F, (1 + |(n : ℝ)|) ^ 2 * ‖diskMode u n r‖ ^ 2) ≤
      2 * (2 * Real.pi)⁻¹ *
        ((∫ r in (1 / 2 : ℝ)..1, ‖diskProfile u r‖ ^ 2) +
         ∫ r in (1 / 2 : ℝ)..1, ‖diskAngularProfile u r‖ ^ 2) := by
  have hi : IntervalIntegrable
      (fun r => ∑ n ∈ F, (1 + |(n : ℝ)|) ^ 2 * ‖diskMode u n r‖ ^ 2)
      volume (1 / 2) 1 := by
    have he : (∑ n ∈ F, fun r : ℝ => (1 + |(n : ℝ)|) ^ 2 * ‖diskMode u n r‖ ^ 2) =
        (fun r => ∑ n ∈ F, (1 + |(n : ℝ)|) ^ 2 * ‖diskMode u n r‖ ^ 2) := by
      funext r
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum F
      (fun n (_ : n ∈ F) => (diskMode_sq_integrable u n).const_mul ((1 + |(n : ℝ)|) ^ 2))
  have h := intervalIntegral.integral_mono_ae_restrict (by norm_num : (1 / 2 : ℝ) ≤ 1)
    hi (((diskProfile_sq_integrable u).add (diskAngularProfile_sq_integrable u)).const_mul
      (2 * (2 * Real.pi)⁻¹)) (by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact diskMode_finite_weight_sq_le_ae u F)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (diskProfile_sq_integrable u) (diskAngularProfile_sq_integrable u)] at h
  exact h

end KsIndex.Trace
