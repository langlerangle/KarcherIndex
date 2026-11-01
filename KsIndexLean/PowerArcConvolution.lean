module

public import KsIndexLean.PowerArcSummability
public import KsIndexLean.ArcSigma

@[expose] public section


/-! Convolution identification for power-arc coefficient sequences. -/
noncomputable section
namespace KsIndex.PowerArc
open Real intervalIntegral Filter Topology MeasureTheory

lemma sec_integral_le_log {x : ℝ} (hx0 : 0 ≤ x) (hx : x < π / 2) :
    (∫ t in (0 : ℝ)..x, 1 / Real.cos t) ≤
      (π / 2) * (Real.log (π / 2) - Real.log (π / 2 - x)) := by
  have hpi := Real.pi_pos
  have ha : (0 : ℝ) < Real.pi / 2 := by linarith
  have hu0 : (0 : ℝ) < Real.pi / 2 - x := by linarith
  have hcospos : ∀ t ∈ Set.Icc (0 : ℝ) x, 0 < Real.cos t := fun t ht =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hI1 : IntervalIntegrable (fun t => 1 / Real.cos t) MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    exact ContinuousOn.div continuousOn_const Real.continuous_cos.continuousOn
      (fun t ht => (hcospos t ht).ne')
  have hI2 : IntervalIntegrable (fun t => (Real.pi / 2) / (Real.pi / 2 - t))
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    exact ContinuousOn.div continuousOn_const (by fun_prop)
      (fun t ht => (sub_pos.mpr (by linarith [ht.2] : t < Real.pi / 2)).ne')
  -- Jordan's inequality gives the pointwise majorant `1/cos t ≤ (π/2)/(π/2 - t)`.
  have hmono : (∫ t in (0 : ℝ)..x, 1 / Real.cos t)
      ≤ ∫ t in (0 : ℝ)..x, (Real.pi / 2) / (Real.pi / 2 - t) := by
    refine intervalIntegral.integral_mono_on hx0 hI1 hI2 (fun t ht => ?_)
    have hc := hcospos t ht
    have hjordan : 2 / Real.pi * (Real.pi / 2 - t) ≤ Real.sin (Real.pi / 2 - t) :=
      Real.mul_le_sin (by linarith [ht.2]) (by linarith [ht.1])
    rw [Real.sin_pi_div_two_sub] at hjordan
    have hat : 0 < Real.pi / 2 - t := by linarith [ht.2]
    rw [div_le_div_iff₀ hc hat]
    have key : (Real.pi / 2) * (2 / Real.pi * (Real.pi / 2 - t)) = Real.pi / 2 - t := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hjordan (le_of_lt (half_pos Real.pi_pos))]
  -- The majorant integrates to `(π/2) log((π/2)/(π/2 - x))`.
  have hval : (∫ t in (0 : ℝ)..x, (Real.pi / 2) / (Real.pi / 2 - t))
      = (Real.pi / 2) * (Real.log (Real.pi / 2) - Real.log (Real.pi / 2 - x)) := by
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (fun s : ℝ => -(Real.pi / 2) * Real.log (Real.pi / 2 - s))
          ((Real.pi / 2) / (Real.pi / 2 - t)) t := by
      intro t ht
      rw [Set.uIcc_of_le hx0] at ht
      have hat : (0 : ℝ) < Real.pi / 2 - t := by linarith [ht.2]
      have h0 : HasDerivAt (fun s : ℝ => Real.pi / 2 - s) (-1) t := by
        exact (hasDerivAt_id t).const_sub (Real.pi / 2)
      have h1 : HasDerivAt (fun s : ℝ => Real.log (Real.pi / 2 - s))
          ((Real.pi / 2 - t)⁻¹ * (-1)) t := (Real.hasDerivAt_log hat.ne').comp t h0
      have h2 := h1.const_mul (-(Real.pi / 2))
      exact h2.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hI2]
    simp
    ring
  exact hmono.trans_eq hval

def logMajorant (x : ℝ) : ℝ := 3 + |Real.log (π / 2)| + |Real.log (π / 2 - x)|

lemma logMajorant_nonneg (x : ℝ) : 0 ≤ logMajorant x := by
  unfold logMajorant
  positivity

lemma logMajorant_integrable : IntervalIntegrable logMajorant volume 0 (π / 2) := by
  have hlog : IntervalIntegrable (fun x : ℝ => Real.log (π / 2 - x)) volume 0 (π / 2) := by
    simpa using (intervalIntegrable_log' (a := (0 : ℝ)) (b := π / 2)).comp_sub_left (π / 2) |>.symm
  exact (intervalIntegrable_const.add intervalIntegrable_const).add hlog.abs

lemma squareWave_log_bound : ∀ᶠ N in atTop, ∀ x : ℝ, 0 ≤ x → x < π / 2 →
    |ArcSigma.T N x| ≤ logMajorant x := by
  filter_upwards [ArcSigma.L_bounded] with N hL
  intro x hx0 hx
  have habs : |x| < π / 2 := by rwa [abs_of_nonneg hx0]
  have hT := ArcSigma.T_eq N habs
  let I : ℝ := ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t
  have hI : |I| ≤ (π / 2) * (Real.log (π / 2) - Real.log (π / 2 - x)) :=
    (ArcSigma.abs_integral_sin_div_cos_le hx0 hx _).trans (sec_integral_le_log hx0 hx)
  have hbound : |ArcSigma.T N x| ≤ 3 + (2 / π) * |I| := by
    rw [hT]
    calc
      _ ≤ |ArcSigma.L N| + |2 / π * (-1 : ℝ) ^ N * I| := abs_sub _ _
      _ = |ArcSigma.L N| + (2 / π) * |I| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ 2 / π by positivity),
          abs_pow, abs_neg, abs_one, one_pow, mul_one]
      _ ≤ _ := by linarith
  have hmul := mul_le_mul_of_nonneg_left hI (show 0 ≤ 2 / π by positivity)
  have heq : 2 / π * ((π / 2) * (Real.log (π / 2) - Real.log (π / 2 - x))) =
      Real.log (π / 2) - Real.log (π / 2 - x) := by field_simp
  rw [heq] at hmul
  unfold logMajorant
  linarith [le_abs_self (Real.log (π / 2)), neg_le_abs (Real.log (π / 2 - x))]

lemma squareWave_tendsto {x : ℝ} (hx0 : 0 ≤ x) (hx : x < π / 2) :
    Tendsto (fun N => ArcSigma.T N x) atTop (𝓝 1) := by
  have habs : |x| < π / 2 := by rwa [abs_of_nonneg hx0]
  have hI : Tendsto
      (fun N : ℕ => ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t)
      atTop (𝓝 0) := by
    have h := SquareWave.tendsto_integral_sin_mul_div_cos hx0 hx
    have hsub : Tendsto (fun N : ℕ => 2 * N + 2) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun N hN => by omega⟩
    refine (h.comp hsub).congr fun N => ?_
    simp only [Function.comp]
    congr 1
    funext t
    push_cast
    ring_nf
  have hsign : Tendsto (fun N : ℕ => 2 / π * (-1 : ℝ) ^ N *
      ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t)
      atTop (𝓝 0) := by
    have hπ : 2 / π ≤ 1 := by
      rw [div_le_one Real.pi_pos]
      linarith [Real.pi_gt_three]
    have hbd : ∀ N : ℕ, ‖2 / π * (-1 : ℝ) ^ N *
        ∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t‖ ≤
        ‖∫ t in (0 : ℝ)..x, Real.sin (2 * ((N : ℝ) + 1) * t) / Real.cos t‖ := by
      intro N
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg,
        abs_one, one_pow, mul_one, abs_of_pos (show 0 < 2 / π by positivity)]
      exact mul_le_of_le_one_left (abs_nonneg _) hπ
    exact squeeze_zero_norm hbd (by simpa using hI.norm)
  have h := ArcSigma.L_tendsto.sub hsign
  simpa only [ArcSigma.T_eq _ habs, sub_zero] using h

theorem kernel_cos_shift (a : ℝ) (m : ℤ) (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc (m - (N : ℤ)) (m + (N : ℤ) + 1),
        ArcKernel.chat' (m - n) * Real.cos ((2 * (n : ℝ) + a) * x)
      = Real.cos ((2 * (m : ℝ) + (a + 1)) * x) *
        (4 / π * ∑ k ∈ Finset.range (N + 1),
          (-1 : ℝ) ^ k * Real.cos ((2 * (k : ℝ) + 1) * x) / (2 * (k : ℝ) + 1)) := by
  rw [ArcKernel.window_reindex m N
    (fun n => ArcKernel.chat' (m - n) * Real.cos ((2 * (n : ℝ) + a) * x))]
  have step : ∀ d : ℤ, ArcKernel.chat' (m - (m - d)) *
      Real.cos ((2 * ((m - d : ℤ) : ℝ) + a) * x)
      = Real.cos ((2 * (m : ℝ) + (a + 1)) * x) *
          (ArcKernel.chat' d * Real.cos ((2 * (d : ℝ) + 1) * x))
        + Real.sin ((2 * (m : ℝ) + (a + 1)) * x) *
          (ArcKernel.chat' d * Real.sin ((2 * (d : ℝ) + 1) * x)) := by
    intro d
    have hm : m - (m - d) = d := by omega
    have harg : (2 * ((m - d : ℤ) : ℝ) + a) * x
        = (2 * (m : ℝ) + (a + 1)) * x - (2 * (d : ℝ) + 1) * x := by push_cast; ring
    rw [hm, harg, Real.cos_sub]; ring
  simp only [step]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ArcKernel.kernel_sin, ArcKernel.kernel_cos]
  ring



def powerIntegrand (β ξ x : ℝ) : ℝ := (Real.cos x) ^ β * Real.cos (ξ * x)

lemma powerIntegrand_continuous {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    Continuous (powerIntegrand β ξ) := by
  exact ((Real.continuous_rpow_const hβ.le).comp Real.continuous_cos).mul (by fun_prop)

lemma powerIntegrand_abs_le_one {β : ℝ} (hβ : 0 < β) (ξ : ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (π / 2)) : |powerIntegrand β ξ x| ≤ 1 := by
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hx.1], hx.2⟩
  have hp : 0 ≤ (Real.cos x) ^ β := Real.rpow_nonneg hc _
  have hp1 : (Real.cos x) ^ β ≤ 1 := Real.rpow_le_one hc (Real.cos_le_one x) hβ.le
  simp only [powerIntegrand, abs_mul, abs_of_nonneg hp]
  exact (mul_le_mul hp1 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (by norm_num)

lemma power_squareWave_integral_tendsto {β : ℝ} (hβ : 0 < β) (ξ : ℝ) :
    Tendsto (fun N => ∫ x in (0 : ℝ)..(π / 2), powerIntegrand β ξ x * ArcSigma.T N x)
      atTop (𝓝 (∫ x in (0 : ℝ)..(π / 2), powerIntegrand β ξ x)) := by
  have hle : (0 : ℝ) ≤ π / 2 := by positivity
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence logMajorant
    ?_ ?_ logMajorant_integrable ?_
  · exact Eventually.of_forall fun N =>
      ((powerIntegrand_continuous hβ ξ).mul (ArcSigma.T_continuous N)).aestronglyMeasurable
  · filter_upwards [squareWave_log_bound] with N hN
    refine ae_of_all _ fun x hx => ?_
    rw [Set.uIoc_of_le hle] at hx
    rcases eq_or_lt_of_le hx.2 with he | hlt
    · subst x
      simp only [powerIntegrand, Real.cos_pi_div_two, Real.zero_rpow hβ.ne', zero_mul, norm_zero]
      exact logMajorant_nonneg _
    · rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ 1 * |ArcSigma.T N x| :=
          mul_le_mul_of_nonneg_right (powerIntegrand_abs_le_one hβ ξ ⟨hx.1.le, hx.2⟩) (abs_nonneg _)
        _ ≤ logMajorant x := by simpa only [one_mul] using hN x hx.1.le hlt
  · refine ae_of_all _ fun x hx => ?_
    rw [Set.uIoc_of_le hle] at hx
    rcases eq_or_lt_of_le hx.2 with he | hlt
    · subst x
      simp only [powerIntegrand, Real.cos_pi_div_two, Real.zero_rpow hβ.ne', zero_mul]
      exact tendsto_const_nhds
    · simpa only [mul_one] using (squareWave_tendsto hx.1.le hlt).const_mul (powerIntegrand β ξ x)

lemma power_partial_sum_eq {β : ℝ} (hβ : 0 < β) (d : ℤ) (m : ℤ) (N : ℕ) :
    (∑ n ∈ ArcSigma.W m N, CircleQ.chat (m - n) * g β (2 * (n : ℝ) + d)) =
      2 * ∫ x in (0 : ℝ)..(π / 2),
        powerIntegrand β (2 * (m : ℝ) + (d + 1)) x * ArcSigma.T N x := by
  have hterm : ∀ n ∈ ArcSigma.W m N,
      CircleQ.chat (m - n) * g β (2 * (n : ℝ) + d) =
      2 * ∫ x in (0 : ℝ)..(π / 2),
        (Real.cos x) ^ β * (CircleQ.chat (m - n) * Real.cos ((2 * (n : ℝ) + d) * x)) := by
    intro n _
    unfold g
    have heq : (fun x : ℝ => (Real.cos x) ^ β *
        (CircleQ.chat (m - n) * Real.cos ((2 * (n : ℝ) + d) * x))) =
        (fun x : ℝ => CircleQ.chat (m - n) *
          ((Real.cos x) ^ β * Real.cos ((2 * (n : ℝ) + d) * x))) := by
      funext x
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    ring
  have hint : ∀ n ∈ ArcSigma.W m N, IntervalIntegrable
      (fun x : ℝ => (Real.cos x) ^ β *
        (CircleQ.chat (m - n) * Real.cos ((2 * (n : ℝ) + d) * x))) volume 0 (π / 2) := by
    intro n _
    apply Continuous.intervalIntegrable
    exact ((Real.continuous_rpow_const hβ.le).comp Real.continuous_cos).mul (by fun_prop)
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← intervalIntegral.integral_finsetSum hint]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← Finset.mul_sum]
  have hk := kernel_cos_shift (d : ℝ) m N x
  have hk' : (∑ n ∈ ArcSigma.W m N, CircleQ.chat (m - n) * Real.cos ((2 * (n : ℝ) + d) * x)) =
      Real.cos ((2 * (m : ℝ) + (d + 1)) * x) * ArcSigma.T N x := by
    simpa only [ArcSigma.W, ArcSigma.T, CircleQ.chat, ArcKernel.chat'] using hk
  rw [hk']
  simp only [powerIntegrand]
  ring

lemma power_convolution_summable {β : ℝ} (hβ : 0 < β) (d m : ℤ) :
    Summable (fun n : ℤ => CircleQ.chat (m - n) * g β (2 * (n : ℝ) + d)) := by
  have ha : Summable (fun n : ℤ => CircleQ.chat (m - n) ^ 2) :=
    SIsometry.summable_chat_sq.comp_injective (fun a b h => by omega)
  have hb := lattice_sq_summable hβ d
  refine Summable.of_norm_bounded ((ha.add hb).mul_left (1 / 2)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|CircleQ.chat (m - n)| - |g β (2 * (n : ℝ) + d)|),
    sq_abs (CircleQ.chat (m - n)), sq_abs (g β (2 * (n : ℝ) + d))]

/-- The full, absolutely convergent convolution identity, for every integer
frequency translate and every positive endpoint exponent. -/
theorem tsum_chat_mul_power {β : ℝ} (hβ : 0 < β) (d m : ℤ) :
    (∑' n : ℤ, CircleQ.chat (m - n) * g β (2 * (n : ℝ) + d)) =
      g β (2 * (m : ℝ) + (d + 1)) := by
  have hW : Tendsto (ArcSigma.W m) atTop atTop :=
    tendsto_atTop_finset_of_monotone (ArcSigma.W_mono m) (ArcSigma.W_cover m)
  have h1 := (power_convolution_summable hβ d m).hasSum.comp hW
  have h2 := (power_squareWave_integral_tendsto hβ (2 * (m : ℝ) + (d + 1))).const_mul 2
  have h2' : Tendsto
      (fun N => ∑ n ∈ ArcSigma.W m N, CircleQ.chat (m - n) * g β (2 * (n : ℝ) + d))
      atTop (𝓝 (g β (2 * (m : ℝ) + (d + 1)))) := by
    simp_rw [power_partial_sum_eq hβ d m]
    simpa only [g, powerIntegrand] using h2
  exact tendsto_nhds_unique h1 h2'

def powerField (β : ℝ) (d : ℤ) (n : ℤ) : ℂ := (g β (2 * (n : ℝ) + d) : ℝ)

@[simp] theorem convS_powerField {β : ℝ} (hβ : 0 < β) (d m : ℤ) :
    CircleQ.convS (powerField β d) m = (g β (2 * (m : ℝ) + (d + 1)) : ℂ) := by
  unfold CircleQ.convS powerField
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, tsum_chat_mul_power hβ]

/-- These are genuine admissible trial fields for the circle form, rather
than only formal coefficient recurrences. -/
theorem powerField_memDom {β : ℝ} (hβ : 0 < β) (d : ℤ) : CircleQ.MemDom (powerField β d) := by
  constructor
  · simpa only [powerField, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      lattice_weighted_summable hβ d 1
  · simp only [convS_powerField hβ, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h := lattice_weighted_summable hβ (d + 1) 4
    simpa only [Int.cast_add, Int.cast_one] using h

/-- Positivity of the two seed integrals used by the recurrence. -/
theorem g_pos_of_mem_unit {β ξ : ℝ} (hβ : 0 < β) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    0 < g β ξ := by
  unfold g
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by positivity : (0 : ℝ) < π / 2)
    (powerIntegrand_continuous hβ ξ).continuousOn
  · intro x hx
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [pi_pos, hx.1], hx.2⟩
    have hcx : 0 ≤ Real.cos (ξ * x) := Real.cos_nonneg_of_mem_Icc
      ⟨by nlinarith [pi_pos, hx.1], by nlinarith [hx.1, hx.2]⟩
    exact mul_nonneg (Real.rpow_nonneg hc _) hcx
  · exact ⟨0, ⟨le_refl _, by positivity⟩, by simp [powerIntegrand]⟩

/-- Parseval identifies the seed ratio without evaluating Gamma functions. -/
theorem even_odd_norm_eq {β : ℝ} (hβ : 0 < β) :
    (∑' n : ℤ, g β (2 * (n : ℝ)) ^ 2) =
      ∑' n : ℤ, g β (2 * (n : ℝ) + 1) ^ 2 := by
  have h := SIsometry.tsum_convS_sq_eq_normSq (powerField_memDom hβ 0)
  simp only [convS_powerField hβ, Int.cast_zero, zero_add, powerField,
    CircleQ.normSq, Complex.norm_real, Real.norm_eq_abs, sq_abs, add_zero] at h
  exact h.symm

def seedScale (β : ℝ) (r : ℤ) : ℝ :=
  ∑' n : ℤ, (g β (2 * (n : ℝ) + r) / g β r) ^ 2

lemma seedScale_summable {β : ℝ} (hβ : 0 < β) (r : ℤ) :
    Summable (fun n : ℤ => (g β (2 * (n : ℝ) + r) / g β r) ^ 2) := by
  simpa only [div_pow] using (lattice_sq_summable hβ r).div_const (g β r ^ 2)

lemma seedScale_pos {β : ℝ} (hβ : 0 < β) {r : ℤ} (hr : g β r ≠ 0) : 0 < seedScale β r := by
  apply (seedScale_summable hβ r).tsum_pos (fun n => sq_nonneg _) 0
  simp [hr]

lemma seedScale_eq {β : ℝ} (r : ℤ) :
    seedScale β r = (∑' n : ℤ, g β (2 * (n : ℝ) + r) ^ 2) / g β r ^ 2 := by
  simp only [seedScale, div_pow, tsum_div_const]

/-- Both normalized sums can be bounded using rational recurrences and exact
tail estimates. Their quotient determines the squared positive seed ratio. -/
theorem seed_ratio_sq {β : ℝ} (hβ : 0 < β) :
    (g β 1 / g β 0) ^ 2 = seedScale β 0 / seedScale β 1 := by
  have h0 := g_pos_of_mem_unit hβ (ξ := 0) (by norm_num) (by norm_num)
  have h1 := g_pos_of_mem_unit hβ (ξ := 1) (by norm_num) (by norm_num)
  have hnorm := even_odd_norm_eq hβ
  have hnormpos : 0 < ∑' n : ℤ, g β (2 * (n : ℝ) + 1) ^ 2 := by
    have h := (lattice_sq_summable hβ 1).tsum_pos (fun n => sq_nonneg _) 0
      (by simpa using sq_pos_of_pos h1)
    simpa only [Int.cast_one] using h
  rw [seedScale_eq, seedScale_eq]
  simp only [Int.cast_zero, Int.cast_one, add_zero]
  rw [hnorm, div_pow]
  field_simp

end KsIndex.PowerArc
