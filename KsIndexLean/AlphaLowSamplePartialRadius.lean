module
public import KsIndexLean.AlphaTrialTableData
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace KsIndex.SamplePartialSumRadius
open KsIndex.AlphaRemarkTrial
open scoped BigOperators
/-- Reflect the shifts separately within the two coefficient families. -/
def reflect : Fin 25 → Fin 25 :=
  ![11,10,9,8,7,6,5,4,3,2,1,0,24,23,22,21,20,19,18,17,16,15,14,13,12]
lemma reflect_involutive : Function.Involutive reflect := by
  intro i
  fin_cases i <;> decide
private lemma reflection_data (i : Fin 25) :
    numerator (reflect i) = numerator i ∧
    seedNumerator (reflect i) = seedNumerator i ∧
    seedRadius (reflect i) = seedRadius i ∧
    |coefficientNumerator (reflect i)| = |coefficientNumerator i| ∧
    shift (reflect i) = -shift i := by
  fin_cases i <;> decide
lemma cell_reflection (t : CoefficientTable) (i : Fin 25) (k : ℤ) :
    tableCellE t (reflect i) (-k) = tableCellE t i k := by
  obtain ⟨hn, hz, hd, _, _⟩ := reflection_data i
  simp only [tableCellE, tableCellA, cellDelta, cellZ, Int.natAbs_neg, hn, hz, hd]
/-- The error radius is even, for every coefficient table; no validity assumption is needed. -/
theorem radius_neg (t : CoefficientTable) (k : ℤ) :
    tableSampleRadius t (-k) = tableSampleRadius t k := by
  let e : Fin 25 ≃ Fin 25 := { toFun := reflect, invFun := reflect, left_inv := reflect_involutive, right_inv := reflect_involutive }
  unfold tableSampleRadius
  apply Fintype.sum_equiv e
  intro i
  obtain ⟨_, _, _, ha, hs⟩ := reflection_data i
  change |coefficientNumerator i| * tableCellE t i (-k + shift i) =
    |coefficientNumerator (reflect i)| * tableCellE t (reflect i) (k + shift (reflect i))
  rw [ha, hs]
  have he : k + -shift i = -(-k + shift i) := by omega
  rw [he, cell_reflection]
#print axioms radius_neg
end KsIndex.SamplePartialSumRadius
