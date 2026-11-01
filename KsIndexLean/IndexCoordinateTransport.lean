module

public import KsIndexLean.FormIndexDensity

@[expose] public section


noncomputable section
namespace KsIndex.NegativeDensity

/-- A full complex-linear change of form coordinates preserves the variational
index. No topological or density surrogate is needed for an equivalence. -/
lemma negativeIndex_linearEquiv {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (e : E ≃ₗ[ℂ] F) (Q : F → ℝ) (hQ : Q 0 = 0) :
    negativeIndex (fun u => Q (e u)) = negativeIndex Q := by
  apply le_antisymm
  · exact negativeIndex_pullback_le Q hQ e.toLinearMap
  · have h := negativeIndex_pullback_le (fun u => Q (e u)) (by simpa using hQ)
      e.symm.toLinearMap
    simpa only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using h

/-- A positive rescaling leaves precisely the same negative subspaces. -/
lemma negativeIndex_pos_mul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Q : E → ℝ) (c : ℝ) (hc : 0 < c) :
    negativeIndex (fun u => c * Q u) = negativeIndex Q := by
  have h (u : E) : c * Q u < 0 ↔ Q u < 0 := by
    constructor
    · intro hn
      nlinarith
    · exact mul_neg_of_pos_of_neg hc
  simp only [negativeIndex, h]

end KsIndex.NegativeDensity
namespace KsIndex.FormIndex

lemma formIndex_eq_of_coordinate_equiv {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    (Q : (ι → ℂ) → ℝ) (D : Submodule ℂ (ι → ℂ)) (e : E ≃ₗ[ℂ] D)
    (hQ : Q 0 = 0) :
    formIndex Q D = NegativeDensity.negativeIndex (fun u => Q (e u)) := by
  rw [formIndex_eq_negativeIndex]
  exact (NegativeDensity.negativeIndex_linearEquiv e (fun u : D => Q u) hQ).symm

end KsIndex.FormIndex
