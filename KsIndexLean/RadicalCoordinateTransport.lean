module

public import KsIndexLean.JacobiRadicalSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [AddCommGroup F] [Module ℂ F]

/-- The weak radical in a new full-domain coordinate system. Its membership
theorem identifies it intrinsically by pairing with every target test vector. -/
def coordinateRadical (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (e : E ≃ₗ[ℂ] F) : Submodule ℂ F :=
  (formRadical Q).map e.toLinearMap

lemma mem_coordinateRadical (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (e : E ≃ₗ[ℂ] F)
    (B : F → F → ℂ) (hB : ∀ u v, B (e u) (e v) = Q u v) (x : F) :
    x ∈ coordinateRadical Q e ↔ ∀ y, B x y = 0 := by
  constructor
  · rintro ⟨u, hu, rfl⟩ y
    obtain ⟨v, rfl⟩ := e.surjective y
    change B (e u) (e v) = 0
    rw [hB]
    exact (mem_formRadical Q u).mp hu v
  · intro hx
    refine ⟨e.symm x, (mem_formRadical Q _).mpr ?_, e.apply_symm_apply x⟩
    intro v
    rw [← hB, e.apply_symm_apply]
    exact hx (e v)

lemma mem_coordinateRadical_scaled (Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (e : E ≃ₗ[ℂ] F) (B : F → F → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hB : ∀ u v, B (e u) (e v) = c * Q u v) (x : F) :
    x ∈ coordinateRadical Q e ↔ ∀ y, B x y = 0 := by
  constructor
  · rintro ⟨u, hu, rfl⟩ y
    obtain ⟨v, rfl⟩ := e.surjective y
    change B (e u) (e v) = 0
    rw [hB, (mem_formRadical Q u).mp hu v, mul_zero]
  · intro hx
    refine ⟨e.symm x, (mem_formRadical Q _).mpr ?_, e.apply_symm_apply x⟩
    intro v
    have h := hx (e v)
    rw [← e.apply_symm_apply x, hB] at h
    exact (mul_eq_zero.mp h).resolve_left hc

def coordinateRadicalEquiv (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (e : E ≃ₗ[ℂ] F) :
    formRadical Q ≃ₗ[ℂ] coordinateRadical Q e :=
  Submodule.equivMapOfInjective e.toLinearMap e.injective (formRadical Q)

lemma coordinateRadical_finrank (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (e : E ≃ₗ[ℂ] F) :
    Module.finrank ℂ (coordinateRadical Q e) = Module.finrank ℂ (formRadical Q) :=
  (coordinateRadicalEquiv Q e).finrank_eq.symm

end KsIndex.Spectral
