module

public import KsIndexLean.KaiOuterRawBound
public import KsIndexLean.AlphaMiddleRemainderEval

@[expose] public section

noncomputable section
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open CircleQ PowerArc OppositeHalf
open KsIndex.Stage2Probe KsIndex.Stage2GrpAe KsIndex.Stage2GrpBo KsIndex.Stage2GrpBe
set_option maxHeartbeats 4000000

theorem rawRemainder_eq_remainderValue (m : ℕ) (hm : 3 ≤ m) :
    rawRemainder (m : ℝ) = remainderValue false m Upos := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have key : (m:ℝ) * rawRemainder (m:ℝ)
      = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_p (m:ℝ)
        + GroupBounds.grpValue_0_1_p (m:ℝ)
        + g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_p (m:ℝ)
        + GroupBounds.grpValue_1_1_p (m:ℝ)
        + (m:ℝ) * Upos / (6*(m:ℝ)+1) := by
    have e := rawRemainder_regrouped (m:ℝ) hm1
    have bAe := bridge_grpAe (m:ℝ) hm3
    have bAo := bridge_grpAo (m:ℝ) hm3
    have bBe := bridge_grpBe (m:ℝ) hm3
    have bBo := bridge_grpBo (m:ℝ) hm3
    rw [e]; linear_combination bAe + bAo + bBe + bBo
  apply mul_left_cancel₀ hmpos.ne'
  rw [key]
  simp [remainderValue, remainderCoefficient, remainderSeed, momentMultiplierQ, Fin.sum_univ_succ]
  field_simp
  ring

theorem rawRemainderNegative_eq_remainderValue (m : ℕ) (hm : 3 ≤ m) :
    rawRemainderNegative (m : ℝ) = remainderValue true m Uneg := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hm3 : (3:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have key : (m:ℝ) * rawRemainderNegative (m:ℝ)
      = g (2161809/5000000:ℝ) 1 / g (2161809/5000000:ℝ) 0 * GroupBounds.grpValue_0_0_m (m:ℝ)
        + GroupBounds.grpValue_0_1_m (m:ℝ)
        + g (2838191/5000000:ℝ) 1 / g (2838191/5000000:ℝ) 0 * GroupBounds.grpValue_1_0_m (m:ℝ)
        + GroupBounds.grpValue_1_1_m (m:ℝ)
        + (m:ℝ) * Uneg / (6*(m:ℝ)-1) := by
    have e := rawRemainderNegative_regrouped (m:ℝ) hm1
    have bAe := KsIndex.Stage2GrpAeNeg.bridge_grpAe_neg (m:ℝ) hm3
    have bAo := KsIndex.Stage2GrpAoNeg.bridge_grpAo_neg (m:ℝ) hm3
    have bBe := KsIndex.Stage2GrpBeNeg.bridge_grpBe_neg (m:ℝ) hm3
    have bBo := KsIndex.Stage2GrpBoNeg.bridge_grpBo_neg (m:ℝ) hm3
    rw [e]; linear_combination bAe + bAo + bBe + bBo
  apply mul_left_cancel₀ hmpos.ne'
  rw [key]
  simp [remainderValue, remainderCoefficient, remainderSeed, momentMultiplierQ, Fin.sum_univ_succ]
  field_simp
  ring

theorem raw_eq_remainderValue (neg : Bool) (m : ℕ) (hm : 3 ≤ m) :
    (if neg then rawRemainderNegative (m : ℝ) else rawRemainder (m : ℝ)) =
      remainderValue neg m (if neg then Uneg else Upos) := by
  cases neg
  · exact rawRemainder_eq_remainderValue m hm
  · exact rawRemainderNegative_eq_remainderValue m hm
end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.raw_eq_remainderValue
