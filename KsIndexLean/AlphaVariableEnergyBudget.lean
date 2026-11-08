module

public import KsIndexLean.AlphaConcreteBudget

@[expose] public section
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc

/-- Any energy floor exceeding the certified residual budget implies the same
strict decimal lower bound on the threshold phase. -/
theorem alphaStar_lower_of_residual_budget_variable {E : ℝ}
    (hR : Summable (fun n : ℤ =>
      headRealResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n))
    (hbudget : (∑' n : ℤ, headRealResidual AlphaRemark.spectralUpper n ^ 2 /
      residualWeight n) < E)
    (henergy : E ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have hs : 0 < AlphaRemark.spectralUpper := by norm_num [AlphaRemark.spectralUpper]
  have hp := gam_pos_of_real_residual_budget hs hR hbudget henergy
  have hstar := Staircase.sstar_lt_of_gam_pos hs hp
  have hphase : 2/Real.pi * Real.arctan (1/AlphaRemark.spectralUpper) < Staircase.alphaStar := by
    exact mul_lt_mul_of_pos_left
      (Real.arctan_strictMono ((one_div_lt_one_div hs Staircase.sstar_pos).mpr hstar))
      (by positivity)
  exact AlphaRemark.phase_lower_endpoint.trans hphase


/-- The existing residual window and outer-tail certificates require only an
energy floor strictly greater than their combined bound of 14/10000000. -/
theorem alphaStar_lower_of_actual_window1025_variable {E : ℝ}
    (hE : (14/10000000 : ℝ) < E)
    (hrawP : ∀ m : ℕ, 1025 < m → |rawRemainder (m:ℝ)| ≤ 1/(m:ℝ))
    (hrawM : ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m:ℝ)| ≤ 1/(m:ℝ))
    (hwindow : (∑ n ∈ residualWindow 1025,
      realResidual AlphaRemark.spectralUpper n^2/residualWeight n) ≤ (7/10000000 : ℝ))
    (henergy : E ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have ht := outer_tail_bound_final AlphaRemark.spectralUpper 1025 (by norm_num)
    1 1 (by norm_num) (by norm_num) hrawP hrawM
  have hb := outer_tail_scalar_budget_from_anchor AlphaRemark.spectralUpper 1 1 1
    1023 1025 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    anchorGroupU anchorGroupU_pos anchorGroupEnergy_bound
  have htail := ht.2.trans (hb.trans concrete_scalar_tail_budget1025)
  have hs := residual_window_tail_sum AlphaRemark.spectralUpper 1025 ht.1
  apply alphaStar_lower_of_residual_budget_variable hs.1 _ henergy
  rw [hs.2]
  have hh := add_le_add hwindow htail
  linarith

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.alphaStar_lower_of_residual_budget_variable
#print axioms KsIndex.AlphaRemarkTrial.alphaStar_lower_of_actual_window1025_variable
