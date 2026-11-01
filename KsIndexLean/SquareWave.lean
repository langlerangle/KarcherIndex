module

/-
Real-analysis identities and bounds for square-wave partial sums.

The finite alternating sine sum gives an integral formula for the cosine
partial sums. Integration by parts proves decay of the oscillatory remainder
at each fixed `0 ≤ x < π/2`. A separate bound controls the endpoint growth
of the reciprocal-cosine integral after multiplication by `√(cos x)`.

Statements and proof sketches by Fable 5; proofs by Aristotle (Harmonic),
project prefix `eef2c6d6`. This module imports only Mathlib.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Real Filter Topology

namespace KsIndex.SquareWave

/-- For `cos t ≠ 0`, the finite alternating sine sum equals
`(−1)^J sin(2(J+1)t)/(2 cos t)`. Induction uses the sine addition formulas. -/
theorem sum_neg_one_pow_mul_sin (J : ℕ) {t : ℝ} (ht : Real.cos t ≠ 0) :
    ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j * Real.sin ((2 * (j : ℝ) + 1) * t)
      = (-1 : ℝ) ^ J * Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t) := by
  induction J with
  | zero => simp [Real.sin_two_mul]; field_simp
  | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      have h1 : (2 : ℝ) * ((J : ℝ) + 1 + 1) * t = (2 * (J : ℝ) + 3) * t + t := by ring
      have h2 : (2 : ℝ) * ((J : ℝ) + 1) * t = (2 * (J : ℝ) + 3) * t - t := by ring
      have h3 : (2 * ((J : ℝ) + 1) + 1) * t = (2 * (J : ℝ) + 3) * t := by ring
      rw [h1, h2, h3, Real.sin_add, Real.sin_sub, pow_succ]
      field_simp
      ring

/-- For `|x| < π/2`, the square-wave cosine partial sum equals its value
at zero minus the integral of its alternating sine sum. The proof integrates
the derivative of the finite sum and applies `sum_neg_one_pow_mul_sin`. -/
theorem square_wave_partial_sum (J : ℕ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ∑ j ∈ Finset.range (J + 1),
        (-1 : ℝ) ^ j * Real.cos ((2 * (j : ℝ) + 1) * x) / (2 * (j : ℝ) + 1)
      = (∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1))
        - (-1 : ℝ) ^ J *
          ∫ t in (0 : ℝ)..x, Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t) := by
  set f : ℝ → ℝ := fun y => ∑ j ∈ Finset.range (J + 1),
        (-1 : ℝ) ^ j * Real.cos ((2 * (j : ℝ) + 1) * y) / (2 * (j : ℝ) + 1) with hf
  set g : ℝ → ℝ := fun y =>
    -∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j * Real.sin ((2 * (j : ℝ) + 1) * y) with hg
  have hcos : ∀ t ∈ Set.uIcc (0 : ℝ) x, Real.cos t > 0 := by
    intro t htm
    have hx1 := abs_lt.1 hx
    rw [Set.uIcc_eq_union] at htm
    have h2 : -(Real.pi / 2) < t ∧ t < Real.pi / 2 := by
      rcases htm with h | h
      · exact ⟨by linarith [h.1], by linarith [h.2, hx1.2]⟩
      · exact ⟨by linarith [h.1, hx1.1], by linarith [h.2]⟩
    exact Real.cos_pos_of_mem_Ioo ⟨h2.1, h2.2⟩
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x, HasDerivAt f (g t) t := by
    intro t _
    have hs : ∀ j ∈ Finset.range (J + 1),
        HasDerivAt (fun y : ℝ => (-1 : ℝ) ^ j * Real.cos ((2 * (j : ℝ) + 1) * y) / (2 * (j : ℝ) + 1))
          (-((-1 : ℝ) ^ j * Real.sin ((2 * (j : ℝ) + 1) * t))) t := by
      intro j _
      have h0 : HasDerivAt (fun y : ℝ => (2 * (j : ℝ) + 1) * y) (2 * (j : ℝ) + 1) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * (j : ℝ) + 1)
      have h1 : HasDerivAt (fun y : ℝ => Real.cos ((2 * (j : ℝ) + 1) * y))
          (-Real.sin ((2 * (j : ℝ) + 1) * t) * (2 * (j : ℝ) + 1)) t :=
        (Real.hasDerivAt_cos _).comp t h0
      have h2 := (h1.const_mul ((-1 : ℝ) ^ j)).div_const (2 * (j : ℝ) + 1)
      have hne : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
      exact h2.congr_deriv (by rw [div_eq_iff hne]; ring)
    simpa [hf, hg, Finset.sum_neg_distrib] using HasDerivAt.fun_sum hs
  have hint : IntervalIntegrable g MeasureTheory.volume 0 x := by
    apply Continuous.intervalIntegrable
    fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr : ∫ t in (0 : ℝ)..x, g t
      = ∫ t in (0 : ℝ)..x, -((-1 : ℝ) ^ J *
          (Real.sin (2 * ((J : ℝ) + 1) * t) / (2 * Real.cos t))) := by
    apply intervalIntegral.integral_congr
    intro t htm
    simp only [hg]
    rw [sum_neg_one_pow_mul_sin J (ne_of_gt (hcos t htm))]
    ring
  rw [hcongr, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at key
  have hf0 : f 0 = ∑ j ∈ Finset.range (J + 1), (-1 : ℝ) ^ j / (2 * (j : ℝ) + 1) := by
    simp [hf]
  rw [hf0] at key
  linarith [key]

/-- For each fixed `0 ≤ x < π/2`, the oscillatory reciprocal-cosine integral
tends to zero as the natural frequency tends to infinity. Integration by parts
bounds its absolute value by `(1/cos x + 1 + x/(cos x)^2)/M` for `M ≥ 1`.
This estimate is not uniform as `x` approaches `π/2`. -/
theorem tendsto_integral_sin_mul_div_cos {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..x, Real.sin ((M : ℝ) * t) / Real.cos t)
      atTop (𝓝 0) := by
  have hpi := Real.pi_pos
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith, hx⟩
  have hcospos : ∀ t ∈ Set.Icc (0 : ℝ) x, 0 < Real.cos t := fun t ht =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcosge : ∀ t ∈ Set.Icc (0 : ℝ) x, Real.cos x ≤ Real.cos t := fun t ht =>
    Real.cos_le_cos_of_nonneg_of_le_pi ht.1 (by linarith) ht.2
  refine squeeze_zero_norm' ?_
    (tendsto_const_div_atTop_nhds_zero_nat (1 / Real.cos x + 1 + x / (Real.cos x) ^ 2))
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hIA : IntervalIntegrable (fun t => Real.sin ((M : ℝ) * t) / Real.cos t)
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hcospos t ht).ne')
  have hIB : IntervalIntegrable
      (fun t => (1 / (M : ℝ)) * (Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2))
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx0]
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun t ht => pow_ne_zero _ (hcospos t ht).ne'))
  -- integration by parts: `-cos(Mt)/(M cos t)` is a primitive up to a `1/M`-small remainder
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun s : ℝ => -(Real.cos ((M : ℝ) * s)) / ((M : ℝ) * Real.cos s))
        (Real.sin ((M : ℝ) * t) / Real.cos t
          - (1 / (M : ℝ)) * (Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hx0] at ht
    have hc := (hcospos t ht).ne'
    have h0 : HasDerivAt (fun s : ℝ => (M : ℝ) * s) (M : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (M : ℝ)
    have hn : HasDerivAt (fun s : ℝ => -(Real.cos ((M : ℝ) * s)))
        ((M : ℝ) * Real.sin ((M : ℝ) * t)) t := by
      exact (((Real.hasDerivAt_cos ((M : ℝ) * t)).comp t h0).neg).congr_deriv (by ring)
    have hd : HasDerivAt (fun s : ℝ => (M : ℝ) * Real.cos s) ((M : ℝ) * (-Real.sin t)) t :=
      (Real.hasDerivAt_cos t).const_mul (M : ℝ)
    have hMne : (M : ℝ) ≠ 0 := hM0.ne'
    exact (hn.div hd (mul_ne_zero hMne hc)).congr_deriv (by
      first | (field_simp; ring) | field_simp | ring)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hIA.sub hIB)
  rw [intervalIntegral.integral_sub hIA hIB, intervalIntegral.integral_const_mul] at key
  have hB : |∫ t in (0 : ℝ)..x, Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2|
      ≤ (1 / (Real.cos x) ^ 2) * x := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := x) (C := 1 / (Real.cos x) ^ 2)
      (f := fun t => Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2) (by
        intro t ht
        rw [Set.uIoc_of_le hx0] at ht
        have htI : t ∈ Set.Icc (0 : ℝ) x := ⟨ht.1.le, ht.2⟩
        have hc := hcospos t htI
        have hge := hcosge t htI
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (Real.cos t) ^ 2)]
        have hnum : |Real.cos ((M : ℝ) * t) * Real.sin t| ≤ 1 := by
          rw [abs_mul]
          nlinarith [Real.abs_cos_le_one ((M : ℝ) * t), Real.abs_sin_le_one t,
            abs_nonneg (Real.cos ((M : ℝ) * t)), abs_nonneg (Real.sin t)]
        have hsq : (Real.cos x) ^ 2 ≤ (Real.cos t) ^ 2 := by nlinarith
        calc |Real.cos ((M : ℝ) * t) * Real.sin t| / (Real.cos t) ^ 2
              ≤ 1 / (Real.cos t) ^ 2 := by gcongr
          _ ≤ 1 / (Real.cos x) ^ 2 := by gcongr)
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hx0] at h
    exact h
  have hFx : |(-(Real.cos ((M : ℝ) * x)) / ((M : ℝ) * Real.cos x))|
      ≤ 1 / ((M : ℝ) * Real.cos x) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (M : ℝ) * Real.cos x), abs_neg]
    gcongr
    exact Real.abs_cos_le_one _
  have hF0 : -(Real.cos ((M : ℝ) * 0)) / ((M : ℝ) * Real.cos 0) = -(1 / (M : ℝ)) := by
    simp; ring
  rw [hF0] at key
  have hA : (∫ t in (0 : ℝ)..x, Real.sin ((M : ℝ) * t) / Real.cos t)
      = (-(Real.cos ((M : ℝ) * x)) / ((M : ℝ) * Real.cos x)) + 1 / (M : ℝ)
      + (1 / (M : ℝ)) * ∫ t in (0 : ℝ)..x,
          Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2 := by
    linarith [key]
  have h1 : |∫ t in (0 : ℝ)..x, Real.sin ((M : ℝ) * t) / Real.cos t|
      ≤ |(-(Real.cos ((M : ℝ) * x)) / ((M : ℝ) * Real.cos x))| + |1 / (M : ℝ)|
      + |(1 / (M : ℝ)) * ∫ t in (0 : ℝ)..x,
          Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2| := by
    rw [hA]; exact abs_add_three _ _ _
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (M : ℝ))] at h1
  have h2 : (1 / (M : ℝ)) *
        |∫ t in (0 : ℝ)..x, Real.cos ((M : ℝ) * t) * Real.sin t / (Real.cos t) ^ 2|
      ≤ (1 / (M : ℝ)) * ((1 / (Real.cos x) ^ 2) * x) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hfinal : 1 / ((M : ℝ) * Real.cos x) + 1 / (M : ℝ)
        + (1 / (M : ℝ)) * ((1 / (Real.cos x) ^ 2) * x)
      = (1 / Real.cos x + 1 + x / (Real.cos x) ^ 2) / (M : ℝ) := by
    field_simp
  rw [Real.norm_eq_abs]
  linarith [h1, hFx, h2, hfinal]

/-- For `0 ≤ x < π/2`, `√(cos x) · ∫₀ˣ dt/cos t ≤ 4`.
Jordan's inequality bounds the integral by a logarithm. The inequality
`log v ≤ v−1`, applied to a square-root ratio, controls that logarithm after
multiplication by `√(π/2−x)`. The final constant uses `√(π/2) ≤ 1.255`. -/
theorem sqrt_cos_mul_integral_inv_cos_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    Real.sqrt (Real.cos x) * (∫ t in (0 : ℝ)..x, 1 / Real.cos t) ≤ 4 := by
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
  have hInonneg : 0 ≤ ∫ t in (0 : ℝ)..x, 1 / Real.cos t :=
    intervalIntegral.integral_nonneg hx0 (fun t ht => (one_div_pos.mpr (hcospos t ht)).le)
  -- `√u · log(a/u) ≤ 2√a` for `0 < u ≤ a = π/2`, and `(π/2)·2√(π/2) = π√(π/2) < 4`.
  have halg : ∀ {u : ℝ}, 0 < u → u ≤ Real.pi / 2 →
      Real.sqrt u * ((Real.pi / 2) * (Real.log (Real.pi / 2) - Real.log u)) ≤ 4 := by
    intro u hu0' hu
    have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0'
    have hsa : 0 < Real.sqrt (Real.pi / 2) := Real.sqrt_pos.mpr ha
    have hlog : Real.log (Real.pi / 2) - Real.log u
        ≤ 2 * (Real.sqrt (Real.pi / 2) / Real.sqrt u - 1) := by
      have h := Real.log_le_sub_one_of_pos
        (show (0 : ℝ) < Real.sqrt (Real.pi / 2) / Real.sqrt u by positivity)
      rw [Real.log_div hsa.ne' hsu.ne', Real.log_sqrt ha.le, Real.log_sqrt hu0'.le] at h
      linarith
    have step1 : Real.sqrt u * ((Real.pi / 2) * (Real.log (Real.pi / 2) - Real.log u))
        ≤ Real.sqrt u * ((Real.pi / 2) * (2 * (Real.sqrt (Real.pi / 2) / Real.sqrt u - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog ha.le) hsu.le
    have heq : Real.sqrt u * ((Real.pi / 2) * (2 * (Real.sqrt (Real.pi / 2) / Real.sqrt u - 1)))
        = Real.pi * (Real.sqrt (Real.pi / 2) - Real.sqrt u) := by field_simp
    have hb : Real.sqrt (Real.pi / 2) ≤ 1.255 := by
      rw [show (1.255 : ℝ) = Real.sqrt (1.255 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
    have hfin : Real.pi * (Real.sqrt (Real.pi / 2) - Real.sqrt u) ≤ 4 := by
      nlinarith [Real.pi_lt_d2, hsu.le, hb]
    rw [heq] at step1
    linarith
  have hsq : Real.sqrt (Real.cos x) ≤ Real.sqrt (Real.pi / 2 - x) := by
    apply Real.sqrt_le_sqrt
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le hu0.le
  calc Real.sqrt (Real.cos x) * (∫ t in (0 : ℝ)..x, 1 / Real.cos t)
      ≤ Real.sqrt (Real.pi / 2 - x) * (∫ t in (0 : ℝ)..x, 1 / Real.cos t) :=
        mul_le_mul_of_nonneg_right hsq hInonneg
    _ ≤ Real.sqrt (Real.pi / 2 - x) *
        ((Real.pi / 2) * (Real.log (Real.pi / 2) - Real.log (Real.pi / 2 - x))) :=
        mul_le_mul_of_nonneg_left (hval ▸ hmono) (Real.sqrt_nonneg _)
    _ ≤ 4 := halg hu0 (by linarith)

end KsIndex.SquareWave
