module

public import KsIndexLean.ProdStepF0R0
public import KsIndexLean.ProdStepF0R1
public import KsIndexLean.ProdStepF1R0
public import KsIndexLean.ProdStepF1R1

@[expose] public section


/-! The generated table is a valid coefficient table at coverage N = 8196. -/
namespace KsIndex.NegSignProd
open KsIndex.AlphaRemarkTrial

theorem valid : ValidCoefficientTable 8196 t := by
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

end KsIndex.NegSignProd
