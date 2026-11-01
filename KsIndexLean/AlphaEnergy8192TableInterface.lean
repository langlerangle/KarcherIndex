module

public import KsIndexLean.AlphaTrialTableLower
public import KsIndexLean.AlphaEnergy8192Contribution

@[expose] public section


/-! Verified integer tables and corrected tails bound the actual trial energy. -/
namespace KsIndex.AlphaRemarkTrial.EnergyWindow8192
open CircleQ

lemma finiteEnergy_eq_windows (s : ℝ) :
    finiteEnergy s =
      (∑ n ∈ Finset.Icc (-8192 : ℤ) 8192, sigP n*‖trial n‖^2) +
        s^2 * ∑ m ∈ Finset.Icc (-8192 : ℤ) 8192, sigM m*‖convS trial m‖^2 := by
  have hp := sum_range_integer_window (fun n => sigP n*‖trial n‖^2) 8192
  have hm := sum_range_integer_window (fun m => sigM m*‖convS trial m‖^2) 8192
  norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd] at hp hm
  unfold finiteEnergy
  rw [hp, hm]

/-- A valid coefficient table covering both finite windows gives this energy
lower bound, including the proved contribution from all four infinite tails. -/
theorem qform_ge_table_and_tails {N : ℕ} {t : CoefficientTable}
    (ht : ValidCoefficientTable N t)
    (hp : ∀ n ∈ Finset.Icc (-8192 : ℤ) 8192, SampleCovered N (2*n))
    (hm : ∀ n ∈ Finset.Icc (-8192 : ℤ) 8192, SampleCovered N (2*n+1)) :
    (((tableEnergyNumerator t (Finset.Icc (-8192) 8192) 1 0 : ℝ) -
        tableEnergyRadius t (Finset.Icc (-8192) 8192) 1 0 +
      (12387581/10000000 : ℝ)^2 *
        ((tableEnergyNumerator t (Finset.Icc (-8192) 8192) 4 1 : ℝ) -
          tableEnergyRadius t (Finset.Icc (-8192) 8192) 4 1)) /
      (10^51 : ℝ)^2) + 140376819/1000000000000 ≤ Qform (12387581/10000000) trial := by
  rw [qform_eq_finite_add_tails]
  refine add_le_add ?_ tails_lower
  rw [finiteEnergy_eq_windows]
  exact finite_trial_energy_ge_table ht _ _ _ hp hm

end KsIndex.AlphaRemarkTrial.EnergyWindow8192
