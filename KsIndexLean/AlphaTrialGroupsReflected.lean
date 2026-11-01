module

public import KsIndexLean.AlphaTrialGroups

@[expose] public section


/-! Reflected trial indices and denominator conditions for the upper moment tail. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

def chainLenR (i : Fin 25) : ℕ := ((-shift i - baseShift i) / 2).toNat

lemma chainLenR_rel (i : Fin 25) :
    (9 + (shift i : ℝ)) + 2 * chainLenR i = baseR i := by
  fin_cases i <;> simp [shift, baseShift, chainLenR, baseR] <;> norm_num

lemma chainLenR_le_six (i : Fin 25) : chainLenR i ≤ 6 := by
  fin_cases i <;> simp [shift, baseShift, chainLenR]

lemma exponent_le_baseterm_refl (i : Fin 25) : exponent i ≤ 9 + (shift i : ℝ) := by
  fin_cases i <;> norm_num [shift, exponent]

lemma denom_smallzR (i : Fin 25) (u : ℕ) (hu : u < chainLenR i) :
    (14/3 : ℝ) + u + 1 - (baseR i - exponent i) / 2 ≠ 0 := by
  have h6 : u < 6 := lt_of_lt_of_le hu (chainLenR_le_six i)
  clear hu
  fin_cases i <;> interval_cases u <;>
    norm_num [baseR, baseShift, shift, exponent]

end KsIndex.OppositeHalf
