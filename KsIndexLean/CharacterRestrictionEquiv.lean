module

public import Mathlib

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

/-- Restrict a linear equivalence on a domain to an additional subspace
condition, using an exact target membership equivalence. -/
def characterRestrictionEquiv
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (D C : Submodule ℂ E) (P : Submodule ℂ F) (e : D ≃ₗ[ℂ] F)
    (h : ∀ u : D, u.val ∈ C ↔ e u ∈ P) : ↥(D ⊓ C) ≃ₗ[ℂ] P where
  toFun u := ⟨e ⟨u, u.property.1⟩, (h ⟨u, u.property.1⟩).mp u.property.2⟩
  invFun v := ⟨(e.symm v.val).val, (e.symm v.val).property,
    (h _).mpr (by rw [e.apply_symm_apply]; exact v.property)⟩
  left_inv u := by
    apply Subtype.ext
    exact congrArg (fun x : D => x.val) (e.symm_apply_apply ⟨u, u.property.1⟩)
  right_inv v := by
    apply Subtype.ext
    exact e.apply_symm_apply v.val
  map_add' u v := by
    apply Subtype.ext
    exact e.map_add ⟨u, u.property.1⟩ ⟨v, v.property.1⟩
  map_smul' c u := by
    apply Subtype.ext
    exact e.map_smul c ⟨u, u.property.1⟩

end KsIndex.Spectral
