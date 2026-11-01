module

public import KsIndexLean.FormIndex
public import KsIndexLean.JacobiRadicalSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.FormIndex

/-- The existing supremum definition of nullity equals the dimension of its
full radical, whenever that radical is finite dimensional. -/
lemma formNullity_eq_finrank_radical {ι : Type*}
    (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D R : Submodule ℂ (ι → ℂ))
    [FiniteDimensional ℂ R]
    (hR : ∀ u, u ∈ R ↔ u ∈ D ∧ ∀ v ∈ D, B u v = 0) :
    formNullity B D = (Module.finrank ℂ R : ℕ∞) := by
  apply le_antisymm
  · refine iSup_le fun V => iSup_le fun hV => iSup_le fun hfd => ?_
    let := hfd
    have hle : V ≤ R := fun u hu => (hR u).mpr ⟨hV.1 hu, hV.2 u hu⟩
    exact_mod_cast Submodule.finrank_mono hle
  · have hnull : NullOn B D R :=
      ⟨fun u hu => ((hR u).mp hu).1, fun u hu => ((hR u).mp hu).2⟩
    exact le_iSup_of_le R (le_iSup_of_le hnull
      (le_iSup_of_le (inferInstance : FiniteDimensional ℂ R) le_rfl))

/-- Transport an intrinsic finite radical through a complex-linear coordinate
identification of the whole form domain. Pairing with all domain vectors is
retained; vanishing of the diagonal alone is not a nullity hypothesis. -/
lemma formNullity_eq_finrank_of_equiv {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ))
    (e : E ≃ₗ[ℂ] D) (R : Submodule ℂ E) [FiniteDimensional ℂ R]
    (hR : ∀ u, u ∈ R ↔ ∀ v, B (e u) (e v) = 0) :
    formNullity B D = (Module.finrank ℂ R : ℕ∞) := by
  let T : E →ₗ[ℂ] (ι → ℂ) := D.subtype.comp e.toLinearMap
  have hT : Function.Injective T := Subtype.val_injective.comp e.injective
  let W := R.map T
  let eqv := Submodule.equivMapOfInjective T hT R
  let : FiniteDimensional ℂ W := eqv.finiteDimensional
  have hW (u : ι → ℂ) : u ∈ W ↔ u ∈ D ∧ ∀ v ∈ D, B u v = 0 := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(e x).property, ?_⟩
      intro v hv
      obtain ⟨y, hy⟩ := e.surjective ⟨v, hv⟩
      have hh := (hR x).mp hx y
      change B (e x) v = 0
      simpa only [hy] using hh
    · rintro ⟨hu, h⟩
      obtain ⟨x, hx⟩ := e.surjective ⟨u, hu⟩
      refine ⟨x, (hR x).mpr ?_, ?_⟩
      · intro v
        simpa only [hx] using h (e v) (e v).property
      · exact congrArg Subtype.val hx
  rw [formNullity_eq_finrank_radical B D W hW, ← eqv.finrank_eq]

/-- The continuous sesquilinear radical used by the solution-operator
construction computes the existing coefficient-domain nullity. -/
lemma formNullity_eq_spectral_radical {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (B : (ι → ℂ) → (ι → ℂ) → ℂ) (D : Submodule ℂ (ι → ℂ))
    (e : E ≃ₗ[ℂ] D) (Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    [FiniteDimensional ℂ (KsIndex.Spectral.formRadical Q)]
    (hQ : ∀ u v, B (e u) (e v) = Q u v) :
    formNullity B D = (Module.finrank ℂ (KsIndex.Spectral.formRadical Q) : ℕ∞) := by
  apply formNullity_eq_finrank_of_equiv B D e
  intro u
  rw [KsIndex.Spectral.mem_formRadical]
  simp only [hQ]

end KsIndex.FormIndex
