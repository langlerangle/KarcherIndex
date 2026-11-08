module
public import KsIndexLean.AlphaEnergy4096Qform
public import KsIndexLean.AlphaVariableEnergyBudget
public import KsIndexLean.AlphaActualWindow1025Assembly
public import KsIndexLean.AlphaMomentBounds
public import KsIndexLean.AlphaActualRemainderIdentity
public import KsIndexLean.AlphaActualOuterBounds
public import KsIndexLean.AlphaRemarkTrialNormalization
@[expose] public section
noncomputable section
namespace KsIndex.AlphaRemarkTrial.Energy4096Decimal
open CircleQ Statements AlphaResidual MiddleInterval MiddleComparison Real

def actualMoment (neg : Bool) : ℝ := if neg then Uneg else Upos
lemma actualMoment_bounds (neg : Bool) :
    (uLo neg : ℝ) ≤ actualMoment neg ∧ actualMoment neg ≤ (uHi neg : ℝ) := by
  cases neg
  · simpa [uLo, uHi, actualMoment] using Upos_row_bounds
  · simpa [uLo, uHi, actualMoment] using Uneg_row_bounds

theorem alphaStar_lower : (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  apply alphaStar_lower_of_actual_window1025_variable (E := 1434/1000000000) (by norm_num)
    rawRemainder_outer_certified rawRemainderNegative_outer_certified
  · apply ActualWindow1025Assembly.window_energy actualMoment actualMoment_bounds
    intro neg n hn _
    simpa only [actualMoment] using MiddleInterval.raw_eq_remainderValue neg n hn
  · simpa only [AlphaRemark.spectralUpper] using EnergyWindow4096.qform_lower

theorem gam_spectralLower_neg : gam AlphaRemark.spectralLower < 0 := by
  have hne : trial ≠ 0 := by
    intro h
    exact trial_head_ne_zero (by simp [h])
  have hpos : 0 < normSq trial := normSq_pos trial_memDom hne
  have hle := GammaOne.gam_le_div (s := AlphaRemark.spectralLower) trial_memDom hpos
  have hQ : Qform AlphaRemark.spectralLower trial < 0 := by
    have h := EnergyWindow4096.qform_upper
    change Qform (12387574/10000000) trial < 0
    exact lt_of_le_of_lt h (by norm_num)
  exact lt_of_le_of_lt hle (div_neg_of_neg_of_pos hQ hpos)

theorem alphaStar_upper : Staircase.alphaStar < (4323619/10000000 : ℝ) := by
  have hL : (0 : ℝ) < AlphaRemark.spectralLower := by norm_num [AlphaRemark.spectralLower]
  have hls := Staircase.lt_sstar_of_gam_neg hL gam_spectralLower_neg
  have h1 : Staircase.alphaStar < 2 / π * arctan (1 / AlphaRemark.spectralLower) := by
    rw [Staircase.alphaStar]
    exact mul_lt_mul_of_pos_left
      (arctan_strictMono ((one_div_lt_one_div Staircase.sstar_pos hL).mpr hls)) (by positivity)
  exact h1.trans AlphaRemark.phase_upper_endpoint
#print axioms alphaStar_lower
#print axioms alphaStar_upper
end KsIndex.AlphaRemarkTrial.Energy4096Decimal
