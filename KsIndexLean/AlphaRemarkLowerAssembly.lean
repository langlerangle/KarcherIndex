module

public import KsIndexLean.AlphaActualWindow1025Assembly
public import KsIndexLean.AlphaEnergy8192Lower
public import KsIndexLean.AlphaConcreteBudget

@[expose] public section


/-! Optional lower-bound assembly using the verified energy and finite-window
certificates. Analytic moment, identity, and outer-remainder suppliers are explicit. -/
namespace KsIndex.AlphaRemarkTrial.LowerAssembly
open CircleQ AlphaResidual MiddleInterval MiddleComparison

theorem alphaStar_lower (U : Bool → ℝ)
    (hU : ∀ neg, (uLo neg : ℝ) ≤ U neg ∧ U neg ≤ (uHi neg : ℝ))
    (hidentity : ∀ neg (n : ℕ), 3 ≤ n → n ≤ 1025 →
      (if neg then rawRemainderNegative (n : ℝ) else rawRemainder (n : ℝ)) =
        remainderValue neg n (U neg))
    (hrawP : ∀ m : ℕ, 1025 < m → |rawRemainder (m : ℝ)| ≤ 1 / (m : ℝ))
    (hrawM : ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m : ℝ)| ≤ 1 / (m : ℝ)) :
    (4323617 / 10000000 : ℝ) < Staircase.alphaStar := by
  apply alphaStar_lower_of_actual_window1025 hrawP hrawM
    (ActualWindow1025Assembly.window_energy U hU hidentity)
  simpa only [AlphaRemark.spectralUpper] using EnergyWindow8192.qform_lower

end KsIndex.AlphaRemarkTrial.LowerAssembly
#print axioms KsIndex.AlphaRemarkTrial.LowerAssembly.alphaStar_lower
