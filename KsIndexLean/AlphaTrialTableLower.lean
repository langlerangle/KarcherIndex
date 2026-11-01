module

public import KsIndexLean.AlphaTrialTableData

@[expose] public section


/-! Lower energy bounds from verified integer tables. -/
namespace KsIndex.AlphaRemarkTrial

/-- Lower bound on the actual finite trial energy from the two integer
component intervals. Infinite tails remain a separate obligation. -/
theorem finite_trial_energy_ge_table {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t) (p q : Finset ℤ) (s : ℝ)
    (hp : ∀ n ∈ p, SampleCovered N (2 * n))
    (hq : ∀ n ∈ q, SampleCovered N (2 * n + 1)) :
    (∑ n ∈ p, CircleQ.sigP n * ‖trial n‖ ^ 2) +
      s ^ 2 * ∑ n ∈ q, CircleQ.sigM n * ‖CircleQ.convS trial n‖ ^ 2 ≥
      ((tableEnergyNumerator t p 1 0 : ℝ) - tableEnergyRadius t p 1 0 +
        s ^ 2 * ((tableEnergyNumerator t q 4 1 : ℝ) - tableEnergyRadius t q 4 1)) /
        (10^51 : ℝ) ^ 2 := by
  have hP := table_integer_energy_component ht p 1 0
    (by simpa only [add_zero] using hp) (by intro n _; omega)
  have hM := table_integer_energy_component ht q 4 1 hq (by intro n _; omega)
  have hP' : ((tableEnergyNumerator t p 1 0 : ℝ) - tableEnergyRadius t p 1 0) /
      (10^51 : ℝ)^2 ≤ ∑ n ∈ p, CircleQ.sigP n * sample (2*n)^2 := by
    have hh := (abs_le.mp hP).1
    simp only [Int.cast_one, add_zero] at hh
    dsimp only [CircleQ.sigP]
    rw [sub_div]
    linarith
  have hM' : ((tableEnergyNumerator t q 4 1 : ℝ) - tableEnergyRadius t q 4 1) /
      (10^51 : ℝ)^2 ≤ ∑ n ∈ q, CircleQ.sigM n * sample (2*n+1)^2 := by
    have hh := (abs_le.mp hM).1
    norm_num only [Int.cast_ofNat, Int.cast_one] at hh
    dsimp only [CircleQ.sigM]
    rw [sub_div]
    linarith
  simp only [trial_eq_sample, convS_eq_sample, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := add_le_add hP' (mul_le_mul_of_nonneg_left hM' (sq_nonneg s))
  convert h using 1 <;> first | rfl | ring

end KsIndex.AlphaRemarkTrial
