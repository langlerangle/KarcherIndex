module

public import KsIndexLean.RadicalCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
variable {G E F : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma radical_product_tests (A : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (B : F →L⋆[ℂ] F →L[ℂ] ℂ) (x : E × F) :
    (∀ y : E × F, A x.1 y.1 + B x.2 y.2 = 0) ↔
      x.1 ∈ formRadical A ∧ x.2 ∈ formRadical B := by
  constructor
  · intro h
    constructor
    · apply (mem_formRadical A x.1).mpr
      intro y
      have hh := h (y, 0)
      simpa only [map_zero, add_zero] using hh
    · apply (mem_formRadical B x.2).mpr
      intro y
      have hh := h (0, y)
      simpa only [map_zero, zero_add] using hh
  · rintro ⟨ha, hb⟩ y
    rw [(mem_formRadical A x.1).mp ha y.1, (mem_formRadical B x.2).mp hb y.2, add_zero]

/-- The full radical of an orthogonal sum is the product of the full radicals.
A common nonzero scale, such as the reflection factor two, has no effect. -/
def radicalProductEquiv (Q : G →L⋆[ℂ] G →L[ℂ] ℂ)
    (A : E →L⋆[ℂ] E →L[ℂ] ℂ) (B : F →L⋆[ℂ] F →L[ℂ] ℂ)
    (e : G ≃ₗ[ℂ] E × F) (c : ℂ) (hc : c ≠ 0)
    (hQ : ∀ u v, Q u v = c * (A (e u).1 (e v).1 + B (e u).2 (e v).2)) :
    formRadical Q ≃ₗ[ℂ] formRadical A × formRadical B := by
  have hm (u : G) : u ∈ formRadical Q ↔
      (e u).1 ∈ formRadical A ∧ (e u).2 ∈ formRadical B := by
    rw [← radical_product_tests A B, mem_formRadical]
    constructor
    · intro h y
      have hh := h (e.symm y)
      rw [hQ, e.apply_symm_apply] at hh
      exact (mul_eq_zero.mp hh).resolve_left hc
    · intro h v
      rw [hQ, h (e v), mul_zero]
  refine
    { toFun := fun u => (⟨(e u.val).1, ((hm u.val).mp u.property).1⟩,
        ⟨(e u.val).2, ((hm u.val).mp u.property).2⟩)
      invFun := fun v => ⟨e.symm (v.1.val, v.2.val), (hm _).mpr (by
        simpa only [e.apply_symm_apply] using And.intro v.1.property v.2.property)⟩
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro u v
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (e.map_add u.val v.val)
    · exact congrArg Prod.snd (e.map_add u.val v.val)
  · intro a u
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (e.map_smul a u.val)
    · exact congrArg Prod.snd (e.map_smul a u.val)
  · intro u
    apply Subtype.ext
    exact e.symm_apply_apply u.val
  · intro v
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (e.apply_symm_apply (v.1.val, v.2.val))
    · exact congrArg Prod.snd (e.apply_symm_apply (v.1.val, v.2.val))

lemma radicalProduct_finrank (Q : G →L⋆[ℂ] G →L[ℂ] ℂ)
    (A : E →L⋆[ℂ] E →L[ℂ] ℂ) (B : F →L⋆[ℂ] F →L[ℂ] ℂ)
    (e : G ≃ₗ[ℂ] E × F) (c : ℂ) (hc : c ≠ 0)
    (hQ : ∀ u v, Q u v = c * (A (e u).1 (e v).1 + B (e u).2 (e v).2))
    [FiniteDimensional ℂ (formRadical A)] [FiniteDimensional ℂ (formRadical B)] :
    Module.finrank ℂ (formRadical Q) =
      Module.finrank ℂ (formRadical A) + Module.finrank ℂ (formRadical B) :=
  (radicalProductEquiv Q A B e c hc hQ).finrank_eq.trans Module.finrank_prod

end KsIndex.Spectral
