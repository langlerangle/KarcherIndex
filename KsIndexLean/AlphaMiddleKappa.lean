module

public import KsIndexLean.AlphaMiddleGroupInputs
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section


/-! Exact outward endpoints used by the middle-window numerical preparation. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval

def kappaLo : ℚ := 9769068109846534480885040042080939995691/10000000000000000000000000000000000000000
def kappaHi : ℚ := 9769068109846534480916135951662609490260/10000000000000000000000000000000000000000

theorem kappaLo_nonneg : 0 ≤ kappaLo := by norm_num [kappaLo]

theorem kappa_enclosed :
    (kappaLo : ℝ) ≤ 2*AlphaRemark.spectralUpper^2/Real.pi ∧
      2*AlphaRemark.spectralUpper^2/Real.pi ≤ (kappaHi : ℝ) := by
  constructor
  · apply (le_div_iff₀ Real.pi_pos).2
    have hp := Real.pi_lt_d20
    norm_num [kappaLo, AlphaRemark.spectralUpper] at *
    nlinarith
  · apply (div_le_iff₀ Real.pi_pos).2
    have hp := Real.pi_gt_d20
    norm_num [kappaHi, AlphaRemark.spectralUpper] at *
    nlinarith

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.kappa_enclosed
