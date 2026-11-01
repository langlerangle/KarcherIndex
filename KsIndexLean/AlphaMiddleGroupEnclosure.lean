module

public import KsIndexLean.AlphaMiddleMultiplierRational
public import KsIndexLean.AlphaMiddleResidualEnclosure

@[expose] public section


/-! Four-group signed enclosure using exact rational multipliers. -/
namespace KsIndex.AlphaRemarkTrial.MiddleInterval
open PowerArc OppositeHalf
set_option maxHeartbeats 4000000

def groupSet : Fin 4 → Finset (Fin 25) :=
  ![{0,2,4,7,9,11}, {1,3,5,6,8,10}, {12,14,16,18,20,22,24}, {13,15,17,19,21,23}]

theorem groupSet_eq : groupSet = ![grpAe, grpAo, grpBe, grpBo] := by
  funext j
  fin_cases j <;> ext i <;> fin_cases i <;>
    norm_num [groupSet, grpAe, grpAo, grpBe, grpBo, exponent, shift] <;> decide
def groupBeta : Fin 4 → ℚ := ![4323618/10000000, 4323618/10000000,
  5676382/10000000, 5676382/10000000]
def groupEndpoint : Fin 4 → ℚ := ![15, 14, 15, 14]

noncomputable def groupValue (s : ℝ) (n : ℕ) (j : Fin 4) : ℝ :=
  compensatedPowerArcGroup (groupBeta j) (groupEndpoint j)
    (2*s^2/Real.pi) (1+s^2) n

def groupMultiplier (n : ℕ) (j : Fin 4) : ℚ :=
  multiplierQ (groupSet j) (groupBeta j) (groupEndpoint j) ((n : ℚ)+9/2)
def groupMultiplierR (n : ℕ) (j : Fin 4) : ℚ :=
  multiplierRQ (groupSet j) (groupBeta j) (groupEndpoint j) ((n : ℚ)+9/2)

theorem allGroups_eq_rational_sum (s : ℝ) (n : ℕ) :
    allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n =
      ∑ j : Fin 4, (groupMultiplier n j : ℝ) * groupValue s n j := by
  simp [groupMultiplier, multiplierQ_cast, groupValue, groupSet_eq, groupBeta,
    groupEndpoint, Fin.sum_univ_succ, allCompensatedGroups, groupCompensated]
  ring

theorem allGroupsR_eq_rational_sum (s : ℝ) (n : ℕ) :
    allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n =
      ∑ j : Fin 4, (groupMultiplierR n j : ℝ) * groupValue s n j := by
  simp [groupMultiplierR, multiplierRQ_cast, groupValue, groupSet_eq, groupBeta,
    groupEndpoint, Fin.sum_univ_succ, allCompensatedGroupsR, groupCompensatedR]
  ring

def groupSumLo (c lo hi : Fin 4 → ℚ) : ℚ := ∑ j, scaleLo (c j) (lo j) (hi j)
def groupSumHi (c lo hi : Fin 4 → ℚ) : ℚ := ∑ j, scaleHi (c j) (lo j) (hi j)

private theorem group_sum_sound (c lo hi : Fin 4 → ℚ) (G : Fin 4 → ℝ)
    (h : ∀ j, (lo j : ℝ) ≤ G j ∧ G j ≤ (hi j : ℝ)) :
    (groupSumLo c lo hi : ℝ) ≤ ∑ j, (c j : ℝ)*G j ∧
      (∑ j, (c j : ℝ)*G j) ≤ (groupSumHi c lo hi : ℝ) := by
  simpa [groupSumLo, groupSumHi] using
    sum_sound Finset.univ _ _ _ (fun j _ => scale_sound (c j) (lo j) (hi j) (G j) (h j))

theorem allGroups_enclosed (s : ℝ) (n : ℕ) (lo hi : Fin 4 → ℚ)
    (h : ∀ j, (lo j : ℝ) ≤ groupValue s n j ∧ groupValue s n j ≤ (hi j : ℝ)) :
    (groupSumLo (groupMultiplier n) lo hi : ℝ) ≤
        allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n ∧
      allCompensatedGroups (2*s^2/Real.pi) (1+s^2) n ≤
        (groupSumHi (groupMultiplier n) lo hi : ℝ) := by
  rw [allGroups_eq_rational_sum]
  exact group_sum_sound _ _ _ _ h

theorem allGroupsR_enclosed (s : ℝ) (n : ℕ) (lo hi : Fin 4 → ℚ)
    (h : ∀ j, (lo j : ℝ) ≤ groupValue s n j ∧ groupValue s n j ≤ (hi j : ℝ)) :
    (groupSumLo (groupMultiplierR n) lo hi : ℝ) ≤
        allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n ∧
      allCompensatedGroupsR (2*s^2/Real.pi) (1+s^2) n ≤
        (groupSumHi (groupMultiplierR n) lo hi : ℝ) := by
  rw [allGroupsR_eq_rational_sum]
  exact group_sum_sound _ _ _ _ h

end KsIndex.AlphaRemarkTrial.MiddleInterval
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.allGroups_enclosed
#print axioms KsIndex.AlphaRemarkTrial.MiddleInterval.allGroupsR_enclosed
