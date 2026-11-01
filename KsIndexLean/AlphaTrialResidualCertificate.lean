module

public import KsIndexLean.AlphaTrialRealResidual
public import KsIndexLean.AlphaRemarkTrialNormalization
public import KsIndexLean.AlphaResidualNonzeroHead
public import KsIndexLean.AlphaRemarkEndpoints

@[expose] public section


/-! The remaining numerical obligation for the actual fixed threshold trial. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual

/-- The real residual on the head-zero test space. -/
def headRealResidual (s : ℝ) (n : ℤ) : ℝ := if n = 0 then 0 else realResidual s n

/-- Exact residual representation with the head removed and coefficients real. -/
theorem trial_Bform_eq_headRealResidual {s : ℝ} {z : ℤ → ℂ}
    (hz : MemDom z) (hz0 : z 0 = 0) :
    Statements.Bform s trial z = ∑' n, (headRealResidual s n : ℂ) * z n := by
  rw [trial_Bform_eq_headZeroResidual hz hz0]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [headRealResidual, hn]
  · simp [headRealResidual, hn, coefficientResidual_trial_eq]

/-- Positivity reduces to the actual real residual's weighted squared norm. -/
theorem gam_pos_of_real_residual {s : ℝ} (hs : 0 < s)
    (hR : Summable (fun n : ℤ => headRealResidual s n ^ 2 / residualWeight n))
    (hmargin : (∑' n : ℤ, headRealResidual s n ^ 2 / residualWeight n) < Qform s trial) :
    0 < gam s := by
  apply gam_pos_of_coefficient_residual_nonzero_head (R := fun n => (headRealResidual s n : ℂ))
    hs trial_memDom trial_head_ne_zero
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hR
  · intro z hz hz0
    exact trial_Bform_eq_headRealResidual hz hz0
  · simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hmargin

/-- A certified energy lower bound can be consumed without normalizing the trial. -/
theorem gam_pos_of_real_residual_budget {s E : ℝ} (hs : 0 < s)
    (hR : Summable (fun n : ℤ => headRealResidual s n ^ 2 / residualWeight n))
    (hbudget : (∑' n : ℤ, headRealResidual s n ^ 2 / residualWeight n) < E)
    (henergy : E ≤ Qform s trial) : 0 < gam s :=
  gam_pos_of_real_residual hs hR (hbudget.trans_le henergy)

/-- The target decimal lower bound, conditional on the remaining numerical residual budget.
The energy premise is kept explicit so the analytic core does not import production tables. -/
theorem alphaStar_lower_of_residual_budget
    (hR : Summable (fun n : ℤ =>
      headRealResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n))
    (hbudget : (∑' n : ℤ, headRealResidual AlphaRemark.spectralUpper n ^ 2 /
      residualWeight n) < (1628/1000000000 : ℝ))
    (henergy : (1628/1000000000 : ℝ) ≤ Qform AlphaRemark.spectralUpper trial) :
    (4323617/10000000 : ℝ) < Staircase.alphaStar := by
  have hs : 0 < AlphaRemark.spectralUpper := by norm_num [AlphaRemark.spectralUpper]
  have hp := gam_pos_of_real_residual_budget hs hR hbudget henergy
  have hstar := Staircase.sstar_lt_of_gam_pos hs hp
  have hphase : 2/Real.pi * Real.arctan (1/AlphaRemark.spectralUpper) < Staircase.alphaStar := by
    exact mul_lt_mul_of_pos_left
      (Real.arctan_strictMono ((one_div_lt_one_div hs Staircase.sstar_pos).mpr hstar))
      (by positivity)
  exact AlphaRemark.phase_lower_endpoint.trans hphase

end KsIndex.AlphaRemarkTrial
