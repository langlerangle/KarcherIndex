module

public import KsIndexLean.AlphaRemarkLowerAssembly
public import KsIndexLean.AlphaMomentBounds

@[expose] public section


/-! Optional lower-bound assembly with the analytic moment suppliers discharged.
The raw-remainder identities and outer estimates remain explicit obligations. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial.LowerAssembly
open CircleQ AlphaResidual MiddleInterval MiddleComparison

def actualMoment (neg : Bool) : ℝ := if neg then Uneg else Upos

theorem actualMoment_bounds (neg : Bool) :
    (uLo neg : ℝ) ≤ actualMoment neg ∧ actualMoment neg ≤ (uHi neg : ℝ) := by
  cases neg
  · simpa [uLo, uHi, actualMoment] using Upos_row_bounds
  · simpa [uLo, uHi, actualMoment] using Uneg_row_bounds

theorem alphaStar_lower_with_moments
    (hidentity : ∀ neg (n : ℕ), 3 ≤ n → n ≤ 1025 →
      (if neg then rawRemainderNegative (n : ℝ) else rawRemainder (n : ℝ)) =
        remainderValue neg n (actualMoment neg))
    (hrawP : ∀ m : ℕ, 1025 < m → |rawRemainder (m : ℝ)| ≤ 1 / (m : ℝ))
    (hrawM : ∀ m : ℕ, 1025 < m → |rawRemainderNegative (m : ℝ)| ≤ 1 / (m : ℝ)) :
    (4323617 / 10000000 : ℝ) < Staircase.alphaStar :=
  alphaStar_lower actualMoment actualMoment_bounds hidentity hrawP hrawM

end KsIndex.AlphaRemarkTrial.LowerAssembly
#print axioms KsIndex.AlphaRemarkTrial.LowerAssembly.alphaStar_lower_with_moments
