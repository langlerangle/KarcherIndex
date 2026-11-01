module

public import KsIndexLean.WeakEndpointEstimate

@[expose] public section


/-! Endpoint control with a variable collar width, for Fourier-mode trace bounds. -/
noncomputable section
open MeasureTheory Set intervalIntegral
namespace KsIndex.Trace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weak integral representative on any nondegenerate interval has an endpoint
bound whose constants retain the interval length. -/
theorem endpoint_length_estimate {a b : ℝ} (hab : a < b) {V g : ℝ → E}
    (hV : ContinuousOn V (Icc a b))
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume a b)
    (hFTC : ∀ r ∈ Icc a b, V b - V r = ∫ t in r..b, g t) :
    (b - a) * ‖V b‖ ^ 2 ≤ 2 * (∫ t in a..b, ‖V t‖ ^ 2) +
      2 * (b - a) ^ 2 * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact (continuous_pow 2).comp_continuousOn hV.norm
  let K := ∫ t in a..b, ‖g t‖ ^ 2
  have hK : 0 ≤ K := intervalIntegral.integral_nonneg hab.le (fun t _ => sq_nonneg _)
  have hpt : ∀ r ∈ Icc a b, ‖V b‖ ^ 2 ≤ 2 * ‖V r‖ ^ 2 + 2 * (b - a) * K := by
    intro r hr
    have hsub : uIcc r b ⊆ uIcc a b := by
      rw [uIcc_of_le hr.2, uIcc_of_le hab.le]
      exact Icc_subset_Icc hr.1 le_rfl
    have hi := norm_integral_sq_le_length_mul hr.2 (hg.mono_set hsub) (hg2.mono_set hsub)
    have ht : (∫ t in r..b, ‖g t‖ ^ 2) ≤ K :=
      intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl
        (Filter.Eventually.of_forall fun t => sq_nonneg ‖g t‖) hg2
    have hi' : ‖V b - V r‖ ^ 2 ≤ (b - a) * K := by
      rw [hFTC r hr]
      exact hi.trans ((mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hr.2)).trans
        (mul_le_mul_of_nonneg_right (by linarith [hr.1]) hK))
    have hn : ‖V b‖ ≤ ‖V r‖ + ‖V b - V r‖ := by
      simpa only [add_sub_cancel] using norm_add_le (V r) (V b - V r)
    have hs := sq_le_sq₀ (norm_nonneg (V b))
      (add_nonneg (norm_nonneg (V r)) (norm_nonneg (V b - V r))) |>.mpr hn
    nlinarith [sq_nonneg (‖V r‖ - ‖V b - V r‖)]
  have h := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
    ((hV2.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hV2.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h
  dsimp [K] at h ⊢
  nlinarith

/-- A frequency-adapted collar estimate. The radial derivative has a uniform
constant while the value term carries the squared frequency. -/
theorem endpoint_frequency_estimate (L : ℝ) (hL : 1 ≤ L) {V g : ℝ → E}
    (hV : ContinuousOn V (Icc (1 / 2 : ℝ) 1))
    (hg : IntervalIntegrable g volume (1 / 2) 1)
    (hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (1 / 2) 1)
    (hFTC : ∀ r ∈ Icc (1 / 2 : ℝ) 1, V 1 - V r = ∫ t in r..1, g t) :
    L * ‖V 1‖ ^ 2 ≤ 4 * L ^ 2 * (∫ t in (1 / 2 : ℝ)..1, ‖V t‖ ^ 2) +
      ∫ t in (1 / 2 : ℝ)..1, ‖g t‖ ^ 2 := by
  have hp : 0 < L := by linarith
  let a := 1 - 1 / (2 * L)
  have hlen : 0 < 1 / (2 * L) := by positivity
  have hsmall : 1 / (2 * L) ≤ 1 / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have ha : 1 / 2 ≤ a := by dsimp [a]; linarith
  have hab : a < 1 := by dsimp [a]; linarith
  have hsub : Icc a 1 ⊆ Icc (1 / 2 : ℝ) 1 := Icc_subset_Icc ha le_rfl
  have husub : uIcc a 1 ⊆ uIcc (1 / 2 : ℝ) 1 := by
    simpa only [uIcc_of_le hab.le, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] using hsub
  have h := endpoint_length_estimate hab (hV.mono hsub) (hg.mono_set husub)
    (hg2.mono_set husub) (fun r hr => hFTC r (hsub hr))
  have hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume (1 / 2) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact (continuous_pow 2).comp_continuousOn hV.norm
  have hvle := intervalIntegral.integral_mono_interval ha hab.le le_rfl
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖V t‖) hV2
  have hgle := intervalIntegral.integral_mono_interval ha hab.le le_rfl
    (Filter.Eventually.of_forall fun t => sq_nonneg ‖g t‖) hg2
  have he : (1 - a) * (2 * L) = 1 := by dsimp [a]; field_simp; ring
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * L ^ 2 by positivity)
  have he2 : (2 * L ^ 2) * (1 - a) = L := by nlinarith
  have he3 : (2 * L ^ 2) * (2 * (1 - a) ^ 2) = 1 := by nlinarith [sq_nonneg ((1-a)*L)]
  have hm' : L * ‖V 1‖ ^ 2 ≤ 4 * L ^ 2 * (∫ t in a..1, ‖V t‖ ^ 2) +
      ∫ t in a..1, ‖g t‖ ^ 2 := by
    rw [← mul_assoc, he2, mul_add,
      ← mul_assoc (2 * L ^ 2) (2 * (1 - a) ^ 2), he3, one_mul] at hm
    nlinarith only [hm]
  nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hvle)]

end KsIndex.Trace
