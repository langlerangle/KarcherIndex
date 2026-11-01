module

public import KsIndexLean.AlphaMiddleRemainderEval

@[expose] public section


/-! Exact signed row endpoints parameterized by the certified moment interval. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open CircleQ AlphaResidual

def rowMode (negative : Bool) (n : ℕ) : ℤ := if negative then -(n : ℤ) else (n : ℤ)
def rowGroupLo (negative : Bool) (n : ℕ) : ℚ :=
  groupSumLo (if negative then groupMultiplierR n else groupMultiplier n)
    (certifiedGroupLo n) (certifiedGroupHi n)
def rowGroupHi (negative : Bool) (n : ℕ) : ℚ :=
  groupSumHi (if negative then groupMultiplierR n else groupMultiplier n)
    (certifiedGroupLo n) (certifiedGroupHi n)
def rowLo (negative : Bool) (n : ℕ) (ul uh : ℚ) : ℚ :=
  residualLo (rowMode negative n) n (rowGroupLo negative n) (rowGroupHi negative n)
    kappaLo kappaHi (remainderLo negative n ul uh) (remainderHi negative n ul uh)
def rowHi (negative : Bool) (n : ℕ) (ul uh : ℚ) : ℚ :=
  residualHi (rowMode negative n) n (rowGroupLo negative n) (rowGroupHi negative n)
    kappaLo kappaHi (remainderLo negative n ul uh) (remainderHi negative n ul uh)

/-- The remaining hypothesis is precisely the analytic raw-remainder identity
with a certified moment interval, not the target residual enclosure. -/
theorem actual_row_enclosed (negative : Bool) (n : ℕ) (hn : 3 ≤ n) (hN : n ≤ 1025)
    (ul uh : ℚ) (U : ℝ) (hU : (ul : ℝ) ≤ U ∧ U ≤ (uh : ℝ))
    (hidentity : (if negative then rawRemainderNegative (n : ℝ) else rawRemainder (n : ℝ)) =
      remainderValue negative n U) :
    (rowLo negative n ul uh : ℝ) ≤ realResidual AlphaRemark.spectralUpper (rowMode negative n) ∧
      realResidual AlphaRemark.spectralUpper (rowMode negative n) ≤ (rowHi negative n ul uh : ℝ) := by
  have hr := remainderValue_enclosed negative n ul uh U hU
  rw [← hidentity] at hr
  cases negative
  · exact realResidual_pos_enclosed _ n hn _ _ _ _ _ _ kappaLo_nonneg
      (certifiedAllGroups_encloses n hn hN) kappa_enclosed hr
  · exact realResidual_neg_enclosed _ n hn _ _ _ _ _ _ kappaLo_nonneg
      (certifiedAllGroupsR_encloses n hn hN) kappa_enclosed hr

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.actual_row_enclosed
