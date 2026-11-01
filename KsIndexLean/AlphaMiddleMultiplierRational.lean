module

public import KsIndexLean.AlphaGroupMultiplierBridgeReflected
public import KsIndexLean.AlphaTrialIntegerData
public import KsIndexLean.PowerArcRational

@[expose] public section


/-! Exact rational evaluators for both transform-chain multipliers.
These identities hold for every rational input, with total field division. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open PowerArc OppositeHalf

def multiplierQ (p : Finset (Fin 25)) (β r z : ℚ) : ℚ :=
  ∑ i ∈ p, ((coefficientNumerator i : ℚ) / 10^12) *
    rationalCoefficient β (2*z-r) (chainLen i)

def multiplierRQ (p : Finset (Fin 25)) (β r z : ℚ) : ℚ :=
  ∑ i ∈ p, ((coefficientNumerator i : ℚ) / 10^12) *
    rationalCoefficient β (2*z-r) (chainLenR i)

theorem multiplierQ_cast (p : Finset (Fin 25)) (β r z : ℚ) :
    (multiplierQ p β r z : ℝ) = trialGroupMult p β r z := by
  rw [trialGroupMult_eq_normalized]
  simp [multiplierQ, coefficient_re_eq, rationalCoefficient_cast]

theorem multiplierRQ_cast (p : Finset (Fin 25)) (β r z : ℚ) :
    (multiplierRQ p β r z : ℝ) = trialGroupMultR p β r z := by
  rw [trialGroupMultR_eq_normalized]
  simp [multiplierRQ, coefficient_re_eq, rationalCoefficient_cast]

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.multiplierQ_cast
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.multiplierRQ_cast
