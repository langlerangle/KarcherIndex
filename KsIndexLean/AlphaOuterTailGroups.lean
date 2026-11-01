module

public import KsIndexLean.AlphaTrialCompensatedResidual
public import KsIndexLean.AlphaTrialCompensatedNegative

@[expose] public section


/-! # Bounds for the four compensated groups

Bound `|allCompensatedGroups κ w n|` and its reflected counterpart by the sum of
four absolute group envelopes, with caps `1/10000`, `491/1000`, `17/20`, and
`3/10000` for A-even, A-odd, B-even, and B-odd respectively. The corresponding
multiplier bounds are hypotheses here. `AlphaMultCapSeam` supplies the forward
caps on the outer range; reflection identities relate the reflected multipliers. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ PowerArc OppositeHalf

/-- Forward: `|allCompensatedGroups|` ≤ Σ_g cap_g · |compensatedPowerArcGroup_g|. -/
theorem allCompensatedGroups_abs_le (κ w : ℝ) (n : ℕ)
    (hAe : |trialGroupMult grpAe (4323618/10000000) 15 ((n : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : |trialGroupMult grpAo (4323618/10000000) 14 ((n : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : |trialGroupMult grpBe (5676382/10000000) 15 ((n : ℝ) + 9/2)| ≤ 17/20)
    (hBo : |trialGroupMult grpBo (5676382/10000000) 14 ((n : ℝ) + 9/2)| ≤ 3/10000) :
    |allCompensatedGroups κ w n| ≤
      1/10000 * |compensatedPowerArcGroup (4323618/10000000) 15 κ w n|
      + 491/1000 * |compensatedPowerArcGroup (4323618/10000000) 14 κ w n|
      + (17/20 * |compensatedPowerArcGroup (5676382/10000000) 15 κ w n|
        + 3/10000 * |compensatedPowerArcGroup (5676382/10000000) 14 κ w n|) := by
  have key : ∀ (p : Finset (Fin 25)) (β r cap : ℝ),
      |trialGroupMult p β r ((n : ℝ) + 9/2)| ≤ cap →
      |groupCompensated p β r κ w n| ≤ cap * |compensatedPowerArcGroup β r κ w n| := by
    intro p β r cap hc
    simp only [groupCompensated, abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hAe' := key grpAe (4323618/10000000) 15 (1/10000) hAe
  have hAo' := key grpAo (4323618/10000000) 14 (491/1000) hAo
  have hBe' := key grpBe (5676382/10000000) 15 (17/20) hBe
  have hBo' := key grpBo (5676382/10000000) 14 (3/10000) hBo
  simp only [allCompensatedGroups]
  have t1 := abs_add_le (groupCompensated grpAe (4323618/10000000) 15 κ w n
      + groupCompensated grpAo (4323618/10000000) 14 κ w n)
    (groupCompensated grpBe (5676382/10000000) 15 κ w n
      + groupCompensated grpBo (5676382/10000000) 14 κ w n)
  have t2 := abs_add_le (groupCompensated grpAe (4323618/10000000) 15 κ w n)
    (groupCompensated grpAo (4323618/10000000) 14 κ w n)
  have t3 := abs_add_le (groupCompensated grpBe (5676382/10000000) 15 κ w n)
    (groupCompensated grpBo (5676382/10000000) 14 κ w n)
  linarith [hAe', hAo', hBe', hBo', t1, t2, t3]

/-- Reflected (negative side): same caps on `trialGroupMultR`. -/
theorem allCompensatedGroupsR_abs_le (κ w : ℝ) (n : ℕ)
    (hAe : |trialGroupMultR grpAe (4323618/10000000) 15 ((n : ℝ) + 9/2)| ≤ 1/10000)
    (hAo : |trialGroupMultR grpAo (4323618/10000000) 14 ((n : ℝ) + 9/2)| ≤ 491/1000)
    (hBe : |trialGroupMultR grpBe (5676382/10000000) 15 ((n : ℝ) + 9/2)| ≤ 17/20)
    (hBo : |trialGroupMultR grpBo (5676382/10000000) 14 ((n : ℝ) + 9/2)| ≤ 3/10000) :
    |allCompensatedGroupsR κ w n| ≤
      1/10000 * |compensatedPowerArcGroup (4323618/10000000) 15 κ w n|
      + 491/1000 * |compensatedPowerArcGroup (4323618/10000000) 14 κ w n|
      + (17/20 * |compensatedPowerArcGroup (5676382/10000000) 15 κ w n|
        + 3/10000 * |compensatedPowerArcGroup (5676382/10000000) 14 κ w n|) := by
  have key : ∀ (p : Finset (Fin 25)) (β r cap : ℝ),
      |trialGroupMultR p β r ((n : ℝ) + 9/2)| ≤ cap →
      |groupCompensatedR p β r κ w n| ≤ cap * |compensatedPowerArcGroup β r κ w n| := by
    intro p β r cap hc
    simp only [groupCompensatedR, abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hAe' := key grpAe (4323618/10000000) 15 (1/10000) hAe
  have hAo' := key grpAo (4323618/10000000) 14 (491/1000) hAo
  have hBe' := key grpBe (5676382/10000000) 15 (17/20) hBe
  have hBo' := key grpBo (5676382/10000000) 14 (3/10000) hBo
  simp only [allCompensatedGroupsR]
  have t1 := abs_add_le (groupCompensatedR grpAe (4323618/10000000) 15 κ w n
      + groupCompensatedR grpAo (4323618/10000000) 14 κ w n)
    (groupCompensatedR grpBe (5676382/10000000) 15 κ w n
      + groupCompensatedR grpBo (5676382/10000000) 14 κ w n)
  have t2 := abs_add_le (groupCompensatedR grpAe (4323618/10000000) 15 κ w n)
    (groupCompensatedR grpAo (4323618/10000000) 14 κ w n)
  have t3 := abs_add_le (groupCompensatedR grpBe (5676382/10000000) 15 κ w n)
    (groupCompensatedR grpBo (5676382/10000000) 14 κ w n)
  linarith [hAe', hAo', hBe', hBo', t1, t2, t3]

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.allCompensatedGroups_abs_le
#print axioms KsIndex.AlphaRemarkTrial.allCompensatedGroupsR_abs_le
