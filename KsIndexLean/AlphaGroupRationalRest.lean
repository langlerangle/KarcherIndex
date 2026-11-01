module

public import KsIndexLean.AlphaTrialCompensatedResidual
public import KsIndexLean.AlphaTrialReducedReflected

@[expose] public section


/-! Rational recurrence coefficients for the finite remainder expressions. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

/-- The forward-chain forcing with its single power-arc factor removed. -/
def zChainForceUnit (β r z : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => ((z+k+1-(r+β+2)/2)/(z+k+1-(r-β)/2))*zChainForceUnit β r z k +
      ((r+β+2)/2-1)/((z+k)*(z+k+1-(r-β)/2))

theorem zChainForce_eq_unit (β r z : ℝ) (k : ℕ) :
    zChainForce β r z k = g β r * zChainForceUnit β r z k := by
  induction k with
  | zero => simp [zChainForce, zChainForceUnit]
  | succ k ih => rw [zChainForce, zChainForceUnit, ih]; ring

/-- Finite rational dependence on supplied normalized endpoint values. -/
def rationalGroupRest (p : Finset (Fin 25)) (β r z : ℝ)
    (c d : Fin 25 → ℝ) (k : Fin 25 → ℕ) (a : ℝ → ℝ) : ℝ :=
  ∑ i ∈ p, c i *
    ((∑ u ∈ Finset.range (k i), (-1 : ℝ)^u * a (d i+2*u)/(z+u)) +
      (-1 : ℝ)^(k i)*a r*zChainForceUnit β r z (k i))

/-- Exact normalization by `g β 0`, without division by the group base value `g β r`. -/
theorem trialGroupRest_normalized (p : Finset (Fin 25)) (β r z : ℝ) :
    trialGroupRest p β r z / g β 0 =
      rationalGroupRest p β r z (fun i => (coefficient i).re)
        (fun i => 9-shift i) chainLen (fun t => g β t/g β 0) := by
  unfold trialGroupRest rationalGroupRest
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [zChainForce_eq_unit]
  have hp : (∑ u ∈ Finset.range (chainLen i),
      (-1 : ℝ)^u * (g β ((9-shift i)+2*u)/g β 0)/(z+u)) =
      (∑ u ∈ Finset.range (chainLen i),
        (-1 : ℝ)^u*g β ((9-shift i)+2*u)/(z+u))/g β 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hp]
  ring

/-- Exact normalization by `g β 0`, without division by the group base value `g β r`. -/
theorem trialGroupRestR_normalized (p : Finset (Fin 25)) (β r z : ℝ) :
    trialGroupRestR p β r z / g β 0 =
      rationalGroupRest p β r z (fun i => (coefficient i).re)
        (fun i => 9+shift i) chainLenR (fun t => g β t/g β 0) := by
  unfold trialGroupRestR rationalGroupRest
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [zChainForce_eq_unit]
  have hp : (∑ u ∈ Finset.range (chainLenR i),
      (-1 : ℝ)^u * (g β ((9+shift i)+2*u)/g β 0)/(z+u)) =
      (∑ u ∈ Finset.range (chainLenR i),
        (-1 : ℝ)^u*g β ((9+shift i)+2*u)/(z+u))/g β 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hp]
  ring

end KsIndex.OppositeHalf

namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

/-- Rational reciprocal correction multiplying the normalized base value. -/
def rationalCorrectionUnit (β r z : ℝ) : ℝ :=
  (((r+β+2)/2-1)/β)/z +
    ((((r+β+2)/2-1)/β)*((r-β)/2)/(1-β))/z^2

theorem groupCorrection_eq_rational (p : Finset (Fin 25)) (β r z : ℝ) :
    groupCorrection p β r z =
      rationalGroupRest p β r z (fun i => (coefficient i).re)
        (fun i => 9-shift i) chainLen (fun t => g β t/g β 0) +
      trialGroupMult p β r z * (g β r/g β 0) * rationalCorrectionUnit β r z := by
  unfold groupCorrection
  rw [trialGroupRest_normalized]
  unfold rationalCorrectionUnit stieltjesCorrectionD stieltjesCorrectionC
  ring

end KsIndex.AlphaRemarkTrial
