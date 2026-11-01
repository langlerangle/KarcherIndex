module

public import KsIndexLean.EndpointRepresentative
public import KsIndexLean.AnnularSpine

@[expose] public section


/-! A quantitative endpoint estimate for Banach-valued integral representatives.
No classical differentiability of the weak derivative is assumed. This is a one-dimensional
estimate, not the assembled trace operator or a polar transport theorem. -/
noncomputable section
open MeasureTheory Set intervalIntegral
namespace KsIndex.Trace

/-- Integral Cauchy–Schwarz on a finite interval, in squared form. -/
lemma integral_sq_le_length_mul {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => f t ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, f t ^ 2 := by
  rcases hab.eq_or_lt with he | hp
  · subst b; simp
  let L := b - a
  let J := ∫ t in a..b, f t
  let c := J / L
  have hL : 0 < L := sub_pos.mpr hp
  have hpoint : ∀ t ∈ Icc a b, 2 * c * f t ≤ f t ^ 2 + c ^ 2 := by
    intro t _
    nlinarith [sq_nonneg (f t - c)]
  have h := intervalIntegral.integral_mono_on hab (hf.const_mul (2 * c))
    (hf2.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hf2 intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at h
  have hc : c * L = J := div_mul_cancel₀ J (ne_of_gt hL)
  change 2 * c * J ≤ (∫ t in a..b, f t ^ 2) + L * c ^ 2 at h
  have hm := mul_le_mul_of_nonneg_right h hL.le
  change J ^ 2 ≤ L * ∫ t in a..b, f t ^ 2
  nlinarith [sq_nonneg (J - c * L)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Bochner integral bound requiring only integrability and square-integrability of the norm. -/
lemma norm_integral_sq_le_length_mul {a b : ℝ} (hab : a ≤ b) {g : ℝ → E}
    (hg : IntervalIntegrable g volume a b)
    (hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume a b) :
    ‖∫ t in a..b, g t‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f := g) (μ := volume) hab
  have hcs := integral_sq_le_length_mul hab hg.norm hg2
  have hn : 0 ≤ ∫ t in a..b, ‖g t‖ :=
    intervalIntegral.integral_nonneg hab (fun t _ => norm_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) hn |>.mpr hnorm).trans hcs

omit [CompleteSpace E] in
/-- An integral representative on [1/2,1] obeys the unweighted endpoint estimate. -/
theorem endpoint_estimate_of_integral {V g : ℝ → E}
    (hV : ContinuousOn V (Icc (1 / 2 : ℝ) 1))
    (hg : IntervalIntegrable g volume (1 / 2) 1)
    (hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (1 / 2) 1)
    (hFTC : ∀ r ∈ Icc (1 / 2 : ℝ) 1, V 1 - V r = ∫ t in r..1, g t) :
    ‖V 1‖ ^ 2 ≤ 4 * (∫ t in (1 / 2 : ℝ)..1, ‖V t‖ ^ 2) +
      ∫ t in (1 / 2 : ℝ)..1, ‖g t‖ ^ 2 := by
  have hh : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume (1 / 2) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hh]
    exact (continuous_pow 2).comp_continuousOn hV.norm
  let K := ∫ t in (1 / 2 : ℝ)..1, ‖g t‖ ^ 2
  have hK : 0 ≤ K := intervalIntegral.integral_nonneg hh (fun t _ => sq_nonneg _)
  have hpt : ∀ r ∈ Icc (1 / 2 : ℝ) 1, ‖V 1‖ ^ 2 ≤ 2 * ‖V r‖ ^ 2 + K := by
    intro r hr
    have hsub : uIcc r 1 ⊆ uIcc (1 / 2 : ℝ) 1 := by
      rw [uIcc_of_le hr.2, uIcc_of_le hh]
      exact Icc_subset_Icc hr.1 le_rfl
    have hi := norm_integral_sq_le_length_mul hr.2 (hg.mono_set hsub) (hg2.mono_set hsub)
    have ht : (∫ t in r..1, ‖g t‖ ^ 2) ≤ K :=
      intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl
        (Filter.Eventually.of_forall fun t => sq_nonneg ‖g t‖) hg2
    have hi' : ‖V 1 - V r‖ ^ 2 ≤ (1 - r) * K := by
      rw [hFTC r hr]
      exact hi.trans (mul_le_mul_of_nonneg_left ht (sub_nonneg.mpr hr.2))
    have hn : ‖V 1‖ ≤ ‖V r‖ + ‖V 1 - V r‖ := by
      simpa only [add_sub_cancel] using norm_add_le (V r) (V 1 - V r)
    have hs := sq_le_sq₀ (norm_nonneg (V 1))
      (add_nonneg (norm_nonneg (V r)) (norm_nonneg (V 1 - V r))) |>.mpr hn
    nlinarith [sq_nonneg (‖V r‖ - ‖V 1 - V r‖), hr.1]
  have h := intervalIntegral.integral_mono_on hh intervalIntegrable_const
    ((hV2.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_add (hV2.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at h
  dsimp [K] at h ⊢
  nlinarith

omit [CompleteSpace E] in
/-- The (8,2) weighted estimate used by the annular trace construction. -/
theorem endpoint_weighted_estimate_of_integral {V g : ℝ → E}
    (hV : ContinuousOn V (Icc (1 / 2 : ℝ) 1))
    (hg : IntervalIntegrable g volume (1 / 2) 1)
    (hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (1 / 2) 1)
    (hFTC : ∀ r ∈ Icc (1 / 2 : ℝ) 1, V 1 - V r = ∫ t in r..1, g t) :
    ‖V 1‖ ^ 2 ≤ 8 * (∫ t in (1 / 2 : ℝ)..1, t * ‖V t‖ ^ 2) +
      2 * ∫ t in (1 / 2 : ℝ)..1, t * ‖g t‖ ^ 2 := by
  have hh : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hV2 : IntervalIntegrable (fun t => ‖V t‖ ^ 2) volume (1 / 2) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hh]
    exact (continuous_pow 2).comp_continuousOn hV.norm
  have h1 := weight_double hV2 (hV2.continuousOn_mul continuousOn_id)
    (fun t _ => sq_nonneg ‖V t‖)
  have h2 := weight_double hg2 (hg2.continuousOn_mul continuousOn_id)
    (fun t _ => sq_nonneg ‖g t‖)
  have h := endpoint_estimate_of_integral hV hg hg2 hFTC
  linarith

/-- The continuous representative satisfies the quantitative bound in the original a.e. data. -/
theorem representative_weighted_endpoint_estimate {f g : ℝ → E}
    (hweak : TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 1) f g 1)
    (hg : IntervalIntegrable g volume (1 / 2) 1)
    (hg2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume (1 / 2) 1) :
    ‖representative (by norm_num : (1 / 2 : ℝ) < 1) f g 1‖ ^ 2 ≤
      8 * (∫ t in (1 / 2 : ℝ)..1, t * ‖f t‖ ^ 2) +
      2 * ∫ t in (1 / 2 : ℝ)..1, t * ‖g t‖ ^ 2 := by
  have hab : (1 / 2 : ℝ) < 1 := by norm_num
  have h := endpoint_weighted_estimate_of_integral
    (representative_continuousOn hab f hg) hg hg2
    (fun r hr => representative_sub_eq_integral hab f hg hr (by norm_num))
  have hae := ae_imp_of_ae_restrict (representative_ae_eq hab hweak hg)
  have heq : (∫ t in (1 / 2 : ℝ)..1, t * ‖representative hab f g t‖ ^ 2) =
      ∫ t in (1 / 2 : ℝ)..1, t * ‖f t‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae, volume.ae_ne (1 : ℝ)] with t ht hne htI
    rw [uIoc_of_le hab.le] at htI
    rw [ht ⟨htI.1, lt_of_le_of_ne htI.2 hne⟩]
  rwa [heq] at h

end KsIndex.Trace
