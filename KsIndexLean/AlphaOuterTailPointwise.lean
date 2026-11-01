module

public import KsIndexLean.AlphaOuterTailGroups
public import KsIndexLean.AlphaTrialResidualCertificate

@[expose] public section


/-! # Pointwise bounds for the residual tail

For `n ≥ 3`, bound `|realResidual s (±n)|` by `sigP(±n)` times the four-group
absolute envelope, plus `(2s²/π) · (D/n)`. The positive and negative sides use
separate raw-remainder bounds. The four multiplier caps and the appropriate
raw-remainder bound are explicit hypotheses of each theorem. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc OppositeHalf

private theorem sigP_pos_of_ne {n : ℤ} (hn : n ≠ 0) : 0 < sigP n := by
  have h := residualWeight_pos n
  rwa [residualWeight, if_neg hn] at h

private theorem absNegOnePow (n : ℕ) : |(-1 : ℝ) ^ n| = 1 := by
  rw [abs_pow]; norm_num

/-- Positive-index pointwise residual bound. -/
theorem realResidual_tail_bound_pos (s : ℝ) (n : ℕ) (hn : 3 ≤ n) (Dp : ℝ)
    (hraw : |rawRemainder (n : ℝ)| ≤ Dp / (n : ℝ))
    (hAe : |trialGroupMult grpAe (4323618/10000000) 15 ((n : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : |trialGroupMult grpAo (4323618/10000000) 14 ((n : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : |trialGroupMult grpBe (5676382/10000000) 15 ((n : ℝ) + 9/2)| ≤ 17/20)
    (hBo : |trialGroupMult grpBo (5676382/10000000) 14 ((n : ℝ) + 9/2)| ≤ 3/10000) :
    |realResidual s (n : ℤ)| ≤
      sigP (n : ℤ) *
        (1/10000 * |compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) n|
          + 491/1000 * |compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) n|
          + (17/20 * |compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) n|
            + 3/10000 * |compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) n|))
      + (2*s^2/Real.pi) * (Dp / (n : ℝ)) := by
  have hn0 : (n : ℤ) ≠ 0 := by omega
  have hsp := sigP_pos_of_ne hn0
  have hC := allCompensatedGroups_abs_le (2*s^2/Real.pi) (1+s^2) n hAe hAo hBe hBo
  have hscaled : |scaledRemainder s (n : ℝ)| ≤ (2*s^2/Real.pi) * (Dp / (n : ℝ)) := by
    rw [scaledRemainder, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*s^2/Real.pi)]
    exact mul_le_mul_of_nonneg_left hraw (by positivity)
  rw [realResidual_eq_compensated s n hn, abs_mul, absNegOnePow, one_mul]
  calc |sigP (n : ℤ) * allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n + scaledRemainder s (n : ℝ)|
      ≤ |sigP (n : ℤ) * allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n| + |scaledRemainder s (n : ℝ)| :=
        abs_add_le _ _
    _ = sigP (n : ℤ) * |allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n| + |scaledRemainder s (n : ℝ)| := by
        rw [abs_mul, abs_of_pos hsp]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hC hsp.le, hscaled]

/-- Negative-index pointwise residual bound. -/
theorem realResidual_tail_bound_neg (s : ℝ) (n : ℕ) (hn : 3 ≤ n) (Dm : ℝ)
    (hraw : |rawRemainderNegative (n : ℝ)| ≤ Dm / (n : ℝ))
    (hAe : |trialGroupMultR grpAe (4323618/10000000) 15 ((n : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : |trialGroupMultR grpAo (4323618/10000000) 14 ((n : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : |trialGroupMultR grpBe (5676382/10000000) 15 ((n : ℝ) + 9/2)| ≤ 17/20)
    (hBo : |trialGroupMultR grpBo (5676382/10000000) 14 ((n : ℝ) + 9/2)| ≤ 3/10000) :
    |realResidual s (-(n : ℤ))| ≤
      sigP (-(n : ℤ)) *
        (1/10000 * |compensatedPowerArcGroup (4323618/10000000) 15 (2*s^2/Real.pi) (1+s^2) n|
          + 491/1000 * |compensatedPowerArcGroup (4323618/10000000) 14 (2*s^2/Real.pi) (1+s^2) n|
          + (17/20 * |compensatedPowerArcGroup (5676382/10000000) 15 (2*s^2/Real.pi) (1+s^2) n|
            + 3/10000 * |compensatedPowerArcGroup (5676382/10000000) 14 (2*s^2/Real.pi) (1+s^2) n|))
      + (2*s^2/Real.pi) * (Dm / (n : ℝ)) := by
  have hn0 : -(n : ℤ) ≠ 0 := by omega
  have hsp := sigP_pos_of_ne hn0
  have hC := allCompensatedGroupsR_abs_le (2*s^2/Real.pi) (1+s^2) n hAe hAo hBe hBo
  have hscaled : |scaledRemainderNegative s (n : ℝ)| ≤ (2*s^2/Real.pi) * (Dm / (n : ℝ)) := by
    rw [scaledRemainderNegative, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*s^2/Real.pi)]
    exact mul_le_mul_of_nonneg_left hraw (by positivity)
  rw [realResidual_neg_eq_compensated s n hn, abs_mul, absNegOnePow, one_mul]
  calc |sigP (-(n : ℤ)) * allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n + scaledRemainderNegative s (n : ℝ)|
      ≤ |sigP (-(n : ℤ)) * allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n|
          + |scaledRemainderNegative s (n : ℝ)| := abs_add_le _ _
    _ = sigP (-(n : ℤ)) * |allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n|
          + |scaledRemainderNegative s (n : ℝ)| := by rw [abs_mul, abs_of_pos hsp]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hC hsp.le, hscaled]

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.realResidual_tail_bound_pos
#print axioms KsIndex.AlphaRemarkTrial.realResidual_tail_bound_neg
