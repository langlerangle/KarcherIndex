module

public import KsIndexLean.AlphaMiddleIntervalArithmetic
public import KsIndexLean.AlphaTrialCompensatedResidual
public import KsIndexLean.AlphaTrialCompensatedNegative

@[expose] public section


/-! Signed middle-mode enclosures from the actual compensated residual identities.
All group and raw-remainder enclosures remain explicit inputs. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open CircleQ AlphaResidual

/-- Preserve cancellation in the signed sum before applying the parity sign. -/
def residualLo (mode : ℤ) (n : ℕ) (gl gh kl kh rl rh : ℚ) : ℚ :=
  scaleLo ((-1 : ℚ)^n)
    (scaleLo (residualWeightRat mode) gl gh + productLo kl kh rl)
    (scaleHi (residualWeightRat mode) gl gh + productHi kl kh rh)

def residualHi (mode : ℤ) (n : ℕ) (gl gh kl kh rl rh : ℚ) : ℚ :=
  scaleHi ((-1 : ℚ)^n)
    (scaleLo (residualWeightRat mode) gl gh + productLo kl kh rl)
    (scaleHi (residualWeightRat mode) gl gh + productHi kl kh rh)

private theorem residual_sound (mode : ℤ) (n : ℕ) (G K R : ℝ)
    (gl gh kl kh rl rh : ℚ) (hm : mode ≠ 0) (hk0 : 0 ≤ kl)
    (hG : (gl : ℝ) ≤ G ∧ G ≤ (gh : ℝ))
    (hK : (kl : ℝ) ≤ K ∧ K ≤ (kh : ℝ))
    (hR : (rl : ℝ) ≤ R ∧ R ≤ (rh : ℝ)) :
    (residualLo mode n gl gh kl kh rl rh : ℝ) ≤ (-1 : ℝ)^n * (sigP mode * G + K*R) ∧
      (-1 : ℝ)^n * (sigP mode * G + K*R) ≤ (residualHi mode n gl gh kl kh rl rh : ℝ) := by
  have hsig : (residualWeightRat mode : ℝ) = sigP mode := by
    rw [residualWeightRat_cast, residualWeight, ite_eq_right hm]
  have hg := scale_sound (residualWeightRat mode) gl gh G hG
  rw [hsig] at hg
  have hr := product_sound kl kh rl rh K R hk0 hK hR
  have hadd : ((scaleLo (residualWeightRat mode) gl gh + productLo kl kh rl : ℚ) : ℝ)
      ≤ sigP mode * G + K*R ∧
      sigP mode * G + K*R ≤
        ((scaleHi (residualWeightRat mode) gl gh + productHi kl kh rh : ℚ) : ℝ) := by
    constructor
    · simpa only [Rat.cast_add] using add_le_add hg.1 hr.1
    · simpa only [Rat.cast_add] using add_le_add hg.2 hr.2
  simpa [residualLo, residualHi] using
    scale_sound ((-1 : ℚ)^n) _ _ _ hadd

/-- Positive middle-mode enclosure; uses the actual residual identity. -/
theorem realResidual_pos_enclosed (s : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (gl gh kl kh rl rh : ℚ) (hk0 : 0 ≤ kl)
    (hG : (gl : ℝ) ≤ allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n ∧
      allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n ≤ (gh : ℝ))
    (hK : (kl : ℝ) ≤ 2*s^2/Real.pi ∧ 2*s^2/Real.pi ≤ (kh : ℝ))
    (hR : (rl : ℝ) ≤ rawRemainder n ∧ rawRemainder n ≤ (rh : ℝ)) :
    (residualLo (n : ℤ) n gl gh kl kh rl rh : ℝ) ≤ realResidual s (n : ℤ) ∧
      realResidual s (n : ℤ) ≤ (residualHi (n : ℤ) n gl gh kl kh rl rh : ℝ) := by
  rw [realResidual_eq_compensated s n hn]
  exact residual_sound (n : ℤ) n _ _ _ gl gh kl kh rl rh (by omega) hk0 hG hK hR

/-- Negative middle-mode enclosure; the reflected group and remainder are
used before the common parity sign is applied. -/
theorem realResidual_neg_enclosed (s : ℝ) (n : ℕ) (hn : 3 ≤ n)
    (gl gh kl kh rl rh : ℚ) (hk0 : 0 ≤ kl)
    (hG : (gl : ℝ) ≤ allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n ∧
      allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n ≤ (gh : ℝ))
    (hK : (kl : ℝ) ≤ 2*s^2/Real.pi ∧ 2*s^2/Real.pi ≤ (kh : ℝ))
    (hR : (rl : ℝ) ≤ rawRemainderNegative n ∧ rawRemainderNegative n ≤ (rh : ℝ)) :
    (residualLo (-(n : ℤ)) n gl gh kl kh rl rh : ℝ) ≤ realResidual s (-(n : ℤ)) ∧
      realResidual s (-(n : ℤ)) ≤ (residualHi (-(n : ℤ)) n gl gh kl kh rl rh : ℝ) := by
  rw [realResidual_neg_eq_compensated s n hn]
  exact residual_sound (-(n : ℤ)) n _ _ _ gl gh kl kh rl rh (by omega) hk0 hG hK hR

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.realResidual_pos_enclosed
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.realResidual_neg_enclosed
