module

public import KsIndexLean.SlitReflectionDecomposition

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- The paper's Neumann character sector, decomposed into both hemisphere
reflection sectors with their exact trace and character conditions. -/
def slitNeumannSubspaceReflectionEquiv (k : ℕ) (C : Submodule ℂ ComplexH1) :
    ↥(slitNeumannDomain k ⊓
      (C.comap (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).toLinearMap ⊓
       C.comap (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).toLinearMap)) ≃ₗ[ℂ]
      C × ↥(zeroTraceDomain (boundaryArc k 1) ⊓ C) := by
  let e := slitNeumannReflectionEquiv k
  have hc (u : slitNeumannDomain k) (hu : u.val.1 ∈ C ∧ u.val.2 ∈ C) :
      (e u).1 ∈ C ∧ (e u).2.val ∈ C := by
    constructor
    · exact C.smul_mem _ (C.add_mem hu.1 hu.2)
    · exact C.smul_mem _ (C.sub_mem hu.1 hu.2)
  refine
    { toFun := fun u => (⟨(e ⟨u.val, u.property.1⟩).1, (hc ⟨u.val, u.property.1⟩ u.property.2).1⟩,
        ⟨(e ⟨u.val, u.property.1⟩).2.val,
          ⟨(e ⟨u.val, u.property.1⟩).2.property, (hc ⟨u.val, u.property.1⟩ u.property.2).2⟩⟩)
      invFun := fun v => ⟨(e.symm (v.1.val, ⟨v.2.val, v.2.property.1⟩)).val,
        ⟨(e.symm _).property, (even_odd_mem_iff C _ _).mpr
          ⟨v.1.property, v.2.property.2⟩⟩⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro u v
    have h := e.map_add ⟨u.val, u.property.1⟩ ⟨v.val, v.property.1⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun w => w.2.val) h
  · intro c u
    have h := e.map_smul c ⟨u.val, u.property.1⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun w => w.2.val) h
  · intro u
    apply Subtype.ext
    exact congrArg (fun w : slitNeumannDomain k => w.val) (e.symm_apply_apply ⟨u.val, u.property.1⟩)
  · intro v
    have h := e.apply_symm_apply (v.1.val, ⟨v.2.val, v.2.property.1⟩)
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst h
    · apply Subtype.ext
      exact congrArg (fun w => w.2.val) h

def paperSlitNeumannCharacterReflectionEquiv (j : ℕ) :
    paperSlitNeumannCharacterDomain j ≃ₗ[ℂ]
      weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j) ×
      ↥(zeroTraceDomain (boundaryArc 3 1) ⊓
        weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) :=
  slitNeumannSubspaceReflectionEquiv 3 _


/-- Moving the slit Dirichlet conditions inside the common hemisphere
subspace preserves both original trace constraints. -/
lemma slitDirichlet_subspace_eq (k : ℕ) (C : Submodule ℂ ComplexH1) :
    slitDirichletDomain k ⊓
      (C.comap (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).toLinearMap ⊓
       C.comap (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).toLinearMap) =
    slitNeumannDomain k ⊓
      ((zeroTraceDomain (boundaryArc k 0) ⊓ C).comap
          (ContinuousLinearMap.fst ℂ ComplexH1 ComplexH1).toLinearMap ⊓
       (zeroTraceDomain (boundaryArc k 0) ⊓ C).comap
          (ContinuousLinearMap.snd ℂ ComplexH1 ComplexH1).toLinearMap) := by
  ext u
  constructor
  · intro h
    exact ⟨h.1.1.1, ⟨⟨h.1.1.2, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩⟩
  · intro h
    exact ⟨⟨⟨h.1, h.2.1.1⟩, h.2.2.1⟩, ⟨h.2.1.2, h.2.2.2⟩⟩

/-- Dirichlet character reflection splitting. The even component vanishes
on arc0; the odd component vanishes on both arcs. Both retain character j. -/
def paperSlitDirichletCharacterReflectionEquiv (j : ℕ) :
    paperSlitDirichletCharacterDomain j ≃ₗ[ℂ]
      ↥(zeroTraceDomain (boundaryArc 3 0) ⊓
        weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) ×
      ↥(zeroTraceDomain (boundaryArc 3 1) ⊓
        (zeroTraceDomain (boundaryArc 3 0) ⊓
          weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))) :=
  (LinearEquiv.ofEq _ _ (slitDirichlet_subspace_eq 3
    (weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)))).trans
    (slitNeumannSubspaceReflectionEquiv 3 _)


lemma paperSlitNeumannCharacterReflection_jacobi (j : ℕ) (V : BoundedRealPotential)
    (u v : ↥(weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) × ↥(zeroTraceDomain (boundaryArc 3 1) ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))) :
    weakJacobi V ((paperSlitNeumannCharacterReflectionEquiv j).symm u).val.1 ((paperSlitNeumannCharacterReflectionEquiv j).symm v).val.1 +
    weakJacobi V ((paperSlitNeumannCharacterReflectionEquiv j).symm u).val.2 ((paperSlitNeumannCharacterReflectionEquiv j).symm v).val.2 =
      2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val) :=
  weakJacobi_even_odd V _ _ _ _

lemma paperSlitNeumannCharacterReflection_mass (j : ℕ)
    (u v : ↥(weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) × ↥(zeroTraceDomain (boundaryArc 3 1) ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j))) :
    inner ℂ (weightedDiskValueCLM ((paperSlitNeumannCharacterReflectionEquiv j).symm u).val.1)
      (weightedDiskValueCLM ((paperSlitNeumannCharacterReflectionEquiv j).symm v).val.1) +
    inner ℂ (weightedDiskValueCLM ((paperSlitNeumannCharacterReflectionEquiv j).symm u).val.2)
      (weightedDiskValueCLM ((paperSlitNeumannCharacterReflectionEquiv j).symm v).val.2) =
      2 * (inner ℂ (weightedDiskValueCLM u.1.val) (weightedDiskValueCLM v.1.val) +
        inner ℂ (weightedDiskValueCLM u.2.val) (weightedDiskValueCLM v.2.val)) :=
  weightedMass_even_odd _ _ _ _

lemma paperSlitDirichletCharacterReflection_jacobi (j : ℕ) (V : BoundedRealPotential)
    (u v : ↥(zeroTraceDomain (boundaryArc 3 0) ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) × ↥(zeroTraceDomain (boundaryArc 3 1) ⊓ (zeroTraceDomain (boundaryArc 3 0) ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)))) :
    weakJacobi V ((paperSlitDirichletCharacterReflectionEquiv j).symm u).val.1 ((paperSlitDirichletCharacterReflectionEquiv j).symm v).val.1 +
    weakJacobi V ((paperSlitDirichletCharacterReflectionEquiv j).symm u).val.2 ((paperSlitDirichletCharacterReflectionEquiv j).symm v).val.2 =
      2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val) :=
  weakJacobi_even_odd V _ _ _ _

lemma paperSlitDirichletCharacterReflection_mass (j : ℕ)
    (u v : ↥(zeroTraceDomain (boundaryArc 3 0) ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)) × ↥(zeroTraceDomain (boundaryArc 3 1) ⊓ (zeroTraceDomain (boundaryArc 3 0) ⊓ weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)))) :
    inner ℂ (weightedDiskValueCLM ((paperSlitDirichletCharacterReflectionEquiv j).symm u).val.1)
      (weightedDiskValueCLM ((paperSlitDirichletCharacterReflectionEquiv j).symm v).val.1) +
    inner ℂ (weightedDiskValueCLM ((paperSlitDirichletCharacterReflectionEquiv j).symm u).val.2)
      (weightedDiskValueCLM ((paperSlitDirichletCharacterReflectionEquiv j).symm v).val.2) =
      2 * (inner ℂ (weightedDiskValueCLM u.1.val) (weightedDiskValueCLM v.1.val) +
        inner ℂ (weightedDiskValueCLM u.2.val) (weightedDiskValueCLM v.2.val)) :=
  weightedMass_even_odd _ _ _ _

end KsIndex.Spectral
