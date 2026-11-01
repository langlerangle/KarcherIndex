module

public import KsIndexLean.AlphaLowProdStepF0R0
public import KsIndexLean.AlphaLowProdStepF0R1
public import KsIndexLean.AlphaLowProdStepF1R0
public import KsIndexLean.AlphaLowProdStepF1R1

@[expose] public section


/-!
Validity of the generated coefficient table `tFast` at coverage `N = 16389`.

The proof uses the trial-family numerators `2161809` and `2838191` and the two
allowed parity indices. For each pair it supplies the imported initial-value
and recurrence-step certificates required by `ValidCoefficientTable`.
The validity statement is scoped by that predicate; it does not certify arbitrary
numerator or parity inputs to the total table accessors.
-/
namespace KsIndex.PositiveEnergyAlphaLowProd
open KsIndex.AlphaRemarkTrial

theorem valid : ValidCoefficientTable 16389 tFast := by
  intro i r hr
  have hnum : numerator i = 2161809 ∨ numerator i = 2838191 := by
    by_cases hi : i.val < 12
    · exact Or.inl (by simp [numerator, hi])
    · exact Or.inr (by simp [numerator, hi])
  interval_cases r
  · rcases hnum with h | h <;> rw [h]
    · exact ⟨zero00, fun n hn => step00 n hn⟩
    · exact ⟨zero10, fun n hn => step10 n hn⟩
  · rcases hnum with h | h <;> rw [h]
    · exact ⟨zero01, fun n hn => step01 n hn⟩
    · exact ⟨zero11, fun n hn => step11 n hn⟩

end KsIndex.PositiveEnergyAlphaLowProd
