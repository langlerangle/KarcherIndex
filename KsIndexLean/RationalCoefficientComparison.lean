module

public import Mathlib

@[expose] public section


/-! Coefficientwise bounds for rational functions on the nonnegative half-line.

Applying these statements after a translation gives uniform bounds past a
specified cutoff. No sampling of the independent variable is involved.
-/

namespace KsIndex

theorem power_sum_pos_of_constant (s : Finset ℕ) (d : ℕ → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hzero : 0 ∈ s) (hd0 : 0 < d 0)
    (hd : ∀ i ∈ s, 0 ≤ d i) : 0 < ∑ i ∈ s, d i * x ^ i := by
  have hh := Finset.single_le_sum
    (fun i hi => mul_nonneg (hd i hi) (pow_nonneg hx i)) hzero
  simp only [pow_zero, mul_one] at hh
  exact lt_of_lt_of_le hd0 hh

theorem rational_coefficient_bounds (s : Finset ℕ) (p d : ℕ → ℝ) (x L U : ℝ)
    (hx : 0 ≤ x) (hden : 0 < ∑ i ∈ s, d i * x ^ i)
    (hlo : ∀ i ∈ s, L * d i ≤ p i)
    (hhi : ∀ i ∈ s, p i ≤ U * d i) :
    L ≤ (∑ i ∈ s, p i * x ^ i) / (∑ i ∈ s, d i * x ^ i) ∧
      (∑ i ∈ s, p i * x ^ i) / (∑ i ∈ s, d i * x ^ i) ≤ U := by
  constructor
  · apply (le_div_iff₀ hden).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hlo i hi) (pow_nonneg hx i)
  · apply (div_le_iff₀ hden).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hhi i hi) (pow_nonneg hx i)

end KsIndex

namespace KsIndex

/-- Integer coefficient certificates give real bounds throughout the nonnegative half-line. -/
theorem rational_integer_coefficients_bound (n : ℕ) (p d : Fin n → ℤ)
    (L U : ℚ) (x : ℝ) (hx : 0 ≤ x)
    (hd : ∀ i, 0 < d i)
    (hn : 0 < n)
    (hlo : ∀ i, L.num * d i ≤ (L.den : ℤ) * p i)
    (hhi : ∀ i, (U.den : ℤ) * p i ≤ U.num * d i) :
    (L : ℝ) ≤ (∑ i, (p i : ℝ) * x ^ i.val) / (∑ i, (d i : ℝ) * x ^ i.val) ∧
      (∑ i, (p i : ℝ) * x ^ i.val) / (∑ i, (d i : ℝ) * x ^ i.val) ≤ (U : ℝ) := by
  have hdp (i : Fin n) : (0 : ℝ) < d i := by exact_mod_cast hd i
  have hden : 0 < ∑ i : Fin n, (d i : ℝ) * x ^ i.val := by
    have hh := Finset.single_le_sum
      (s := Finset.univ) (f := fun i : Fin n => (d i : ℝ) * x ^ i.val)
      (fun i _ => mul_nonneg (hdp i).le (pow_nonneg hx _))
      (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    simp only [pow_zero, mul_one] at hh
    exact lt_of_lt_of_le (hdp ⟨0, hn⟩) hh
  have hlo' (i : Fin n) : (L : ℝ) * d i ≤ p i := by
    have hh : (L.num : ℝ) * d i ≤ (L.den : ℝ) * p i := by exact_mod_cast hlo i
    rw [← Rat.num_div_den L, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by exact_mod_cast L.pos)).2
    simpa only [mul_comm] using hh
  have hhi' (i : Fin n) : (p i : ℝ) ≤ (U : ℝ) * d i := by
    have hh : (U.den : ℝ) * p i ≤ (U.num : ℝ) * d i := by exact_mod_cast hhi i
    rw [← Rat.num_div_den U, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by exact_mod_cast U.pos)).2
    simpa only [mul_comm] using hh
  constructor
  · apply (le_div_iff₀ hden).2
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hlo' i) (pow_nonneg hx _)
  · apply (div_le_iff₀ hden).2
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hhi' i) (pow_nonneg hx _)

end KsIndex
