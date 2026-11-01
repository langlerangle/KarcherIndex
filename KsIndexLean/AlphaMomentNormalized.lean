module

public import KsIndexLean.AlphaTrialMomentReduced
public import KsIndexLean.AlphaGroupSeedRest

@[expose] public section


/-! Normalize the eight moment groups before rational interval evaluation. -/
noncomputable section
namespace KsIndex.OppositeHalf
open PowerArc KsIndex.AlphaRemarkTrial

/-- Each group depends on one normalized transform and one common odd seed. -/
def momentGroup (reflected : Bool) (p : Finset (Fin 25))
    (β : ℝ) (r : ℤ) (z seed transform : ℝ) : ℝ :=
  if reflected then
    trialGroupMultR p β r z * transform +
      seededGroupRest p β r z seed (fun i => (coefficient i).re)
        (fun i => 9 + shift i) chainLenR
  else
    trialGroupMult p β r z * transform +
      seededGroupRest p β r z seed (fun i => (coefficient i).re)
        (fun i => 9 - shift i) chainLen

theorem momentGroup_forward (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β)
    (r : ℤ) (z : ℝ) :
    (trialGroupMult p β r z * powerArcStieltjes β r z + trialGroupRest p β r z) /
      g β 0 = momentGroup false p β r z (g β 1/g β 0)
        (powerArcStieltjes β r z/g β 0) := by
  simp only [momentGroup, Bool.false_eq_true, ↓reduceIte]
  rw [add_div, trialGroupRest_eq_seeded p hβ]
  ring

theorem momentGroup_reflected (p : Finset (Fin 25)) {β : ℝ} (hβ : 0 < β)
    (r : ℤ) (z : ℝ) :
    (trialGroupMultR p β r z * powerArcStieltjes β r z + trialGroupRestR p β r z) /
      g β 0 = momentGroup true p β r z (g β 1/g β 0)
        (powerArcStieltjes β r z/g β 0) := by
  simp only [momentGroup, ↓reduceIte]
  rw [add_div, trialGroupRestR_eq_seeded p hβ]
  ring

/-- The four normalized groups at a fixed moment coordinate. -/
def normalizedMoment (reflected : Bool) (z : ℝ) : ℝ :=
  momentGroup reflected grpAe (4323618/10000000) 15 z
    (g (4323618/10000000) 1/g (4323618/10000000) 0)
    (powerArcStieltjes (4323618/10000000) 15 z/g (4323618/10000000) 0) +
  momentGroup reflected grpAo (4323618/10000000) 14 z
    (g (4323618/10000000) 1/g (4323618/10000000) 0)
    (powerArcStieltjes (4323618/10000000) 14 z/g (4323618/10000000) 0) +
  momentGroup reflected grpBe (5676382/10000000) 15 z
    (g (5676382/10000000) 1/g (5676382/10000000) 0)
    (powerArcStieltjes (5676382/10000000) 15 z/g (5676382/10000000) 0) +
  momentGroup reflected grpBo (5676382/10000000) 14 z
    (g (5676382/10000000) 1/g (5676382/10000000) 0)
    (powerArcStieltjes (5676382/10000000) 14 z/g (5676382/10000000) 0)

theorem reducedMomentLower_eq_normalized (z : ℝ) :
    reducedMomentLower z = normalizedMoment false z := by
  unfold normalizedMoment
  norm_num only
  have h := momentGroup_forward grpAe (β := 4323618/10000000) (by norm_num) 15 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  have h := momentGroup_forward grpAo (β := 4323618/10000000) (by norm_num) 14 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  have h := momentGroup_forward grpBe (β := 5676382/10000000) (by norm_num) 15 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  have h := momentGroup_forward grpBo (β := 5676382/10000000) (by norm_num) 14 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  unfold reducedMomentLower
  norm_num only
  ring

theorem reducedMomentUpper_eq_normalized (z : ℝ) :
    reducedMomentUpper z = normalizedMoment true z := by
  unfold normalizedMoment
  norm_num only
  have h := momentGroup_reflected grpAe (β := 4323618/10000000) (by norm_num) 15 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  have h := momentGroup_reflected grpAo (β := 4323618/10000000) (by norm_num) 14 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  have h := momentGroup_reflected grpBe (β := 5676382/10000000) (by norm_num) 15 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  have h := momentGroup_reflected grpBo (β := 5676382/10000000) (by norm_num) 14 z
  norm_num only [Int.cast_ofNat] at h
  rw [← h]
  unfold reducedMomentUpper
  norm_num only
  ring

end KsIndex.OppositeHalf
#print axioms KsIndex.OppositeHalf.momentGroup_forward
#print axioms KsIndex.OppositeHalf.momentGroup_reflected

#print axioms KsIndex.OppositeHalf.reducedMomentLower_eq_normalized
#print axioms KsIndex.OppositeHalf.reducedMomentUpper_eq_normalized
