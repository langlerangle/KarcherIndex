module

public import KsIndexLean.PowerArcRational

@[expose] public section


/-! Kernel-checked numerical intervals for the power-arc seed sums. -/

namespace KsIndex.PowerArc

set_option maxRecDepth 10000

set_option maxHeartbeats 2000000 in
-- Exact rational recurrence evaluation requires an increased tactic budget.
theorem gamma_even_sum_bounds :
    (1038193353447 / 1000000000000 : ℝ) ≤
      ∑' n : ℕ, normalizedCoefficient (2161809 / 5000000) 0 n ^ 2 ∧
    (∑' n : ℕ, normalizedCoefficient (2161809 / 5000000) 0 n ^ 2) ≤
      1038193354654 / 1000000000000 := by
  have hb := rational_sum_bounds (2161809 / 5000000) 0 64
    (by norm_num) (by norm_num)
    (by simpa using (g_pos_of_mem_unit (β := (2161809 / 5000000 : ℝ))
      (ξ := 0) (by norm_num) (by norm_num) (by norm_num)).ne')
    (by norm_num) (by norm_num [rationalError])
  have hl : (1038193353447 / 1000000000000 : ℚ) ≤ rationalLower (2161809 / 5000000) 0 64 := by
    norm_num [rationalLower, rationalPartial, rationalTail, rationalCoefficient,
      Finset.sum_range_succ]
  have hu : rationalUpper (2161809 / 5000000) 0 64 ≤ (1038193354654 / 1000000000000 : ℚ) := by
    norm_num [rationalUpper, rationalPartial, rationalTail, rationalError,
      rationalCoefficient, Finset.sum_range_succ]
  have hl' : (1038193353447 / 1000000000000 : ℝ) ≤
      (rationalLower (2161809 / 5000000) 0 64 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hl
  have hu' : (rationalUpper (2161809 / 5000000) 0 64 : ℝ) ≤
      (1038193354654 / 1000000000000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hu
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_zero, Int.cast_one] at hb
  exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩

set_option maxHeartbeats 2000000 in
-- Exact rational recurrence evaluation requires an increased tactic budget.
theorem gamma_odd_sum_bounds :
    (1039077178916 / 1000000000000 : ℝ) ≤
      ∑' n : ℕ, normalizedCoefficient (2161809 / 5000000) 1 n ^ 2 ∧
    (∑' n : ℕ, normalizedCoefficient (2161809 / 5000000) 1 n ^ 2) ≤
      1039077182384 / 1000000000000 := by
  have hb := rational_sum_bounds (2161809 / 5000000) 1 64
    (by norm_num) (by norm_num)
    (by simpa using (g_pos_of_mem_unit (β := (2161809 / 5000000 : ℝ))
      (ξ := 1) (by norm_num) (by norm_num) (by norm_num)).ne')
    (by norm_num) (by norm_num [rationalError])
  have hl : (1039077178916 / 1000000000000 : ℚ) ≤ rationalLower (2161809 / 5000000) 1 64 := by
    norm_num [rationalLower, rationalPartial, rationalTail, rationalCoefficient,
      Finset.sum_range_succ]
  have hu : rationalUpper (2161809 / 5000000) 1 64 ≤ (1039077182384 / 1000000000000 : ℚ) := by
    norm_num [rationalUpper, rationalPartial, rationalTail, rationalError,
      rationalCoefficient, Finset.sum_range_succ]
  have hl' : (1039077178916 / 1000000000000 : ℝ) ≤
      (rationalLower (2161809 / 5000000) 1 64 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hl
  have hu' : (rationalUpper (2161809 / 5000000) 1 64 : ℝ) ≤
      (1039077182384 / 1000000000000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hu
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_zero, Int.cast_one] at hb
  exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩

set_option maxHeartbeats 2000000 in
-- Exact rational recurrence evaluation requires an increased tactic budget.
theorem beta_even_sum_bounds :
    (1056273399064 / 1000000000000 : ℝ) ≤
      ∑' n : ℕ, normalizedCoefficient (2838191 / 5000000) 0 n ^ 2 ∧
    (∑' n : ℕ, normalizedCoefficient (2838191 / 5000000) 0 n ^ 2) ≤
      1056273399629 / 1000000000000 := by
  have hb := rational_sum_bounds (2838191 / 5000000) 0 64
    (by norm_num) (by norm_num)
    (by simpa using (g_pos_of_mem_unit (β := (2838191 / 5000000 : ℝ))
      (ξ := 0) (by norm_num) (by norm_num) (by norm_num)).ne')
    (by norm_num) (by norm_num [rationalError])
  have hl : (1056273399064 / 1000000000000 : ℚ) ≤ rationalLower (2838191 / 5000000) 0 64 := by
    norm_num [rationalLower, rationalPartial, rationalTail, rationalCoefficient,
      Finset.sum_range_succ]
  have hu : rationalUpper (2838191 / 5000000) 0 64 ≤ (1056273399629 / 1000000000000 : ℚ) := by
    norm_num [rationalUpper, rationalPartial, rationalTail, rationalError,
      rationalCoefficient, Finset.sum_range_succ]
  have hl' : (1056273399064 / 1000000000000 : ℝ) ≤
      (rationalLower (2838191 / 5000000) 0 64 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hl
  have hu' : (rationalUpper (2838191 / 5000000) 0 64 : ℝ) ≤
      (1056273399629 / 1000000000000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hu
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_zero, Int.cast_one] at hb
  exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩

set_option maxHeartbeats 2000000 in
-- Exact rational recurrence evaluation requires an increased tactic budget.
theorem beta_odd_sum_bounds :
    (1019605863065 / 1000000000000 : ℝ) ≤
      ∑' n : ℕ, normalizedCoefficient (2838191 / 5000000) 1 n ^ 2 ∧
    (∑' n : ℕ, normalizedCoefficient (2838191 / 5000000) 1 n ^ 2) ≤
      1019605863719 / 1000000000000 := by
  have hb := rational_sum_bounds (2838191 / 5000000) 1 64
    (by norm_num) (by norm_num)
    (by simpa using (g_pos_of_mem_unit (β := (2838191 / 5000000 : ℝ))
      (ξ := 1) (by norm_num) (by norm_num) (by norm_num)).ne')
    (by norm_num) (by norm_num [rationalError])
  have hl : (1019605863065 / 1000000000000 : ℚ) ≤ rationalLower (2838191 / 5000000) 1 64 := by
    norm_num [rationalLower, rationalPartial, rationalTail, rationalCoefficient,
      Finset.sum_range_succ]
  have hu : rationalUpper (2838191 / 5000000) 1 64 ≤ (1019605863719 / 1000000000000 : ℚ) := by
    norm_num [rationalUpper, rationalPartial, rationalTail, rationalError,
      rationalCoefficient, Finset.sum_range_succ]
  have hl' : (1019605863065 / 1000000000000 : ℝ) ≤
      (rationalLower (2838191 / 5000000) 1 64 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hl
  have hu' : (rationalUpper (2838191 / 5000000) 1 64 : ℝ) ≤
      (1019605863719 / 1000000000000 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hu
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_zero, Int.cast_one] at hb
  exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩

/-- A certified squared seed ratio for the endpoint-adapted trial exponent. -/
theorem gamma_seed_ratio_bounds :
    (517953200 / 1000000000 : ℝ) < (g (2161809 / 5000000) 1 / g (2161809 / 5000000) 0) ^ 2 ∧
    (g (2161809 / 5000000) 1 / g (2161809 / 5000000) 0) ^ 2 < 517953206 / 1000000000 := by
  have h := seed_ratio_bounds_of_sum_bounds (by norm_num : (0 : ℝ) < 2161809 / 5000000)
    (by norm_num) (by norm_num) gamma_even_sum_bounds.1 gamma_even_sum_bounds.2
    gamma_odd_sum_bounds.1 gamma_odd_sum_bounds.2
  norm_num at h
  constructor <;> linarith [h.1, h.2]

/-- A certified squared seed ratio for the endpoint-adapted trial exponent. -/
theorem beta_seed_ratio_bounds :
    (545576892 / 1000000000 : ℝ) < (g (2838191 / 5000000) 1 / g (2838191 / 5000000) 0) ^ 2 ∧
    (g (2838191 / 5000000) 1 / g (2838191 / 5000000) 0) ^ 2 < 545576895 / 1000000000 := by
  have h := seed_ratio_bounds_of_sum_bounds (by norm_num : (0 : ℝ) < 2838191 / 5000000)
    (by norm_num) (by norm_num) beta_even_sum_bounds.1 beta_even_sum_bounds.2
    beta_odd_sum_bounds.1 beta_odd_sum_bounds.2
  norm_num at h
  constructor <;> linarith [h.1, h.2]

end KsIndex.PowerArc
