module

public import KsIndexLean.AlphaMiddleRowComparisonAssembly
public import KsIndexLean.AlphaLowProductionEnergy

@[expose] public section


/-! Optional finite-window assembly. Moment bounds and raw-remainder identities
remain explicit premises; this is not an unconditional alphaStar bound. -/
namespace KsIndex.AlphaRemarkTrial.ActualWindow1025Assembly
open CircleQ AlphaResidual MiddleInterval MiddleComparison

theorem window_energy (U : Bool → ℝ)
    (hU : ∀ neg, (uLo neg : ℝ) ≤ U neg ∧ U neg ≤ (uHi neg : ℝ))
    (hidentity : ∀ neg (n : ℕ), 3 ≤ n → n ≤ 1025 →
      (if neg then rawRemainderNegative (n : ℝ) else rawRemainder (n : ℝ)) =
        remainderValue neg n (U neg)) :
    (∑ n ∈ residualWindow 1025,
      realResidual AlphaRemark.spectralUpper n ^ 2 / residualWeight n) ≤
        (7 / 10000000 : ℝ) :=
  actual_window1025_of_low_middle LowProduction.low_energy
    (MiddleComparisonAssembly.middle_energy U hU hidentity)

end KsIndex.AlphaRemarkTrial.ActualWindow1025Assembly
#print axioms KsIndex.AlphaRemarkTrial.ActualWindow1025Assembly.window_energy
