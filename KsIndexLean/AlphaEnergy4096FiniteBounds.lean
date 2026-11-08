module
public import KsIndexLean.AlphaTrialTableLower
public import KsIndexLean.AlphaEnergyWindow4096
public import KsIndexLean.AlphaEnergy4096FinitePCenter
public import KsIndexLean.AlphaEnergy4096FinitePRadius
public import KsIndexLean.AlphaEnergy4096FiniteMmCenter
public import KsIndexLean.AlphaEnergy4096FiniteMmRadius
@[expose] public section
namespace KsIndex.AlphaRemarkTrial.EnergyWindow4096
open CircleQ Energy4096Finite
lemma finiteEnergy_eq_windows (s : ℝ) :
    finiteEnergy s =
      (∑ n ∈ Finset.Icc (-4096 : ℤ) 4096, sigP n*‖trial n‖^2) +
        s^2 * ∑ m ∈ Finset.Icc (-4096 : ℤ) 4096, sigM m*‖convS trial m‖^2 := by
  have hp := sum_range_integer_window (fun n => sigP n*‖trial n‖^2) 4096
  have hm := sum_range_integer_window (fun m => sigM m*‖convS trial m‖^2) 4096
  norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd] at hp hm
  unfold finiteEnergy
  rw [hp, hm]
lemma covered_P (n : ℤ) (hn : n ∈ Finset.Icc (-4096 : ℤ) 4096) : SampleCovered 8196 (2*n) := by
  apply sampleCovered_of_bound
  simp only [Finset.mem_Icc] at hn
  omega
lemma covered_Mm (n : ℤ) (hn : n ∈ Finset.Icc (-4096 : ℤ) 4096) : SampleCovered 8196 (2*n+1) := by
  apply sampleCovered_of_bound
  simp only [Finset.mem_Icc] at hn
  omega
theorem finite_lower (s : ℝ) : ((-1885573365124354241746324758615444742181937662879431565011871407281476032021177378539117234135063261163 : ℝ) - 37198672267181531537015126558447518359680932461078379329440693334190851251411707408140076541311 + s^2 * ((1228598556460330154678468728001578844023920182169567159376397256847375291016624896207636780963882719194 : ℝ) - 8408478407363723289053895100780696174642654168301390583391401221740109366247607045469716014249)) / (10^51 : ℝ)^2 ≤ finiteEnergy s := by
  rw [finiteEnergy_eq_windows]
  have h := finite_trial_energy_ge_table KsIndex.NegSignProd.valid (Finset.Icc (-4096) 4096) (Finset.Icc (-4096) 4096) s covered_P covered_Mm
  rw [window_P_center, window_P_radius, window_Mm_center, window_Mm_radius] at h
  norm_num only [Int.cast_ofNat, Int.cast_neg] at h ⊢
  exact h
#print axioms finite_lower
theorem finite_upper (s : ℝ) : ((-1885573365124354241746324758615444742181937662879431565011871407281476032021177378539117234135063261163 : ℝ) + 37198672267181531537015126558447518359680932461078379329440693334190851251411707408140076541311 + s^2 * ((1228598556460330154678468728001578844023920182169567159376397256847375291016624896207636780963882719194 : ℝ) + 8408478407363723289053895100780696174642654168301390583391401221740109366247607045469716014249)) / (10^51 : ℝ)^2 ≥ finiteEnergy s := by
  rw [finiteEnergy_eq_windows]
  have h := finite_trial_energy_le_table KsIndex.NegSignProd.valid (Finset.Icc (-4096) 4096) (Finset.Icc (-4096) 4096) s covered_P covered_Mm
  rw [window_P_center, window_P_radius, window_Mm_center, window_Mm_radius] at h
  norm_num only [Int.cast_ofNat, Int.cast_neg] at h ⊢
  exact h
#print axioms finite_upper
end KsIndex.AlphaRemarkTrial.EnergyWindow4096
