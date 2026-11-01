module

public import KsIndexLean.RadicalProduct
public import KsIndexLean.SlitCharacterReflection
public import KsIndexLean.IndexNullityBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

def diskWeakNullity (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) : ℕ :=
  Module.finrank ℂ (@formRadical D inferInstance (diskDomain_innerProductSpace D)
    (domainJacobiForm D V))

lemma pair_reflection_nullity (D : Submodule ℂ DiskPairH1)
    (A B : Submodule ℂ ComplexH1) [CompleteSpace A] [CompleteSpace B]
    (V : BoundedRealPotential) (e : D ≃ₗ[ℂ] A × B)
    (h : ∀ u v : A × B,
      weakJacobi V (e.symm u).val.1 (e.symm v).val.1 +
      weakJacobi V (e.symm u).val.2 (e.symm v).val.2 =
      2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val)) :
    finiteCopyWeakNullity (pairFiniteDomain D) V = diskWeakNullity A V + diskWeakNullity B V := by
  let f := (pairHilbertCoordinates D).trans e
  have hQ (u v : finiteH1Domain (pairFiniteDomain D)) :
      finiteJacobiForm (pairFiniteDomain D) V u v =
      (2 : ℂ) * (domainJacobiForm A V (f u).1 (f v).1 +
        domainJacobiForm B V (f u).2 (f v).2) := by
    have hh := h (e (pairHilbertCoordinates D u)) (e (pairHilbertCoordinates D v))
    have he := congrArg₂ (fun x y : D =>
      weakJacobi V x.val.1 y.val.1 + weakJacobi V x.val.2 y.val.2)
      (e.symm_apply_apply (pairHilbertCoordinates D u))
      (e.symm_apply_apply (pairHilbertCoordinates D v))
    exact (finiteJacobiForm_apply (pairFiniteDomain D) V u v).trans
      ((pairFiniteJacobi_eq D V u v).trans (he.symm.trans hh))
  exact @radicalProduct_finrank (finiteH1Domain (pairFiniteDomain D)) A B
    inferInstance (finiteH1Domain_innerProductSpace _) inferInstance (diskDomain_innerProductSpace A)
    inferInstance (diskDomain_innerProductSpace B)
    (finiteJacobiForm (pairFiniteDomain D) V) (domainJacobiForm A V) (domainJacobiForm B V)
    f 2 (by norm_num) hQ (diskRadical_finiteDimensional A V) (diskRadical_finiteDimensional B V)

abbrev paperHemisphereCharacter (j : ℕ) : Submodule ℂ ComplexH1 :=
  weakCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)

abbrev paperNeumannOddCharacter (j : ℕ) : Submodule ℂ ComplexH1 :=
  zeroTraceDomain (boundaryArc 3 1) ⊓ paperHemisphereCharacter j

instance paperNeumannOddCharacter_complete (j : ℕ) : CompleteSpace (paperNeumannOddCharacter j) :=
  ((isClosed_zeroTraceDomain _).inter (isClosed_weakCharacterDomain _ _)).isComplete.completeSpace_coe

/-- Nullity of the actual Neumann character slit form is the sum of the two
full hemisphere weak nullities. -/
lemma paperSlitNeumannCharacter_nullity (j : ℕ) (V : BoundedRealPotential) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V =
      diskWeakNullity (paperHemisphereCharacter j) V +
      diskWeakNullity (paperNeumannOddCharacter j) V :=
  pair_reflection_nullity _ _ _ V (paperSlitNeumannCharacterReflectionEquiv j)
    (paperSlitNeumannCharacterReflection_jacobi j V)


abbrev paperDirichletEvenCharacter (j : ℕ) : Submodule ℂ ComplexH1 :=
  zeroTraceDomain (boundaryArc 3 0) ⊓ paperHemisphereCharacter j

abbrev paperDirichletOddCharacter (j : ℕ) : Submodule ℂ ComplexH1 :=
  zeroTraceDomain (boundaryArc 3 1) ⊓ paperDirichletEvenCharacter j

instance paperDirichletEvenCharacter_complete (j : ℕ) : CompleteSpace (paperDirichletEvenCharacter j) :=
  ((isClosed_zeroTraceDomain _).inter (isClosed_weakCharacterDomain _ _)).isComplete.completeSpace_coe

instance paperDirichletOddCharacter_complete (j : ℕ) : CompleteSpace (paperDirichletOddCharacter j) :=
  ((isClosed_zeroTraceDomain _).inter
    ((isClosed_zeroTraceDomain _).inter (isClosed_weakCharacterDomain _ _))).isComplete.completeSpace_coe

lemma paperSlitDirichletCharacter_nullity (j : ℕ) (V : BoundedRealPotential) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V =
      diskWeakNullity (paperDirichletEvenCharacter j) V +
      diskWeakNullity (paperDirichletOddCharacter j) V :=
  pair_reflection_nullity _ _ _ V (paperSlitDirichletCharacterReflectionEquiv j)
    (paperSlitDirichletCharacterReflection_jacobi j V)

end KsIndex.Spectral
