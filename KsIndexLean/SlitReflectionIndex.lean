module

public import KsIndexLean.DiskFiniteNegativeCoordinates
public import KsIndexLean.SlitHemisphereDomains

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

lemma diskJacobi_product_index (A B : Submodule ℂ ComplexH1)
    [CompleteSpace A] [CompleteSpace B] (V : BoundedRealPotential) :
    negativeIndex (fun u : A × B => (weakJacobi V u.1 u.1).re + (weakJacobi V u.2 u.2).re) =
      negativeIndex (fun u : A => (weakJacobi V u u).re) +
      negativeIndex (fun u : B => (weakJacobi V u u).re) := by
  by_cases hA : FiniteDimensional ℂ (WeightedDiskAmbient A)
  · let := hA
    by_cases hB : FiniteDimensional ℂ (WeightedDiskAmbient B)
    · let := hB
      exact diskJacobi_product_index_finite A B V
    · let := (diskSpectralData B V).eigenbasisIndex_infinite hB
      exact diskJacobi_product_index_finite_infinite A B V
  · let := (diskSpectralData A V).eigenbasisIndex_infinite hA
    by_cases hB : FiniteDimensional ℂ (WeightedDiskAmbient B)
    · let := hB
      exact diskJacobi_product_index_infinite_finite A B V
    · let := (diskSpectralData B V).eigenbasisIndex_infinite hB
      exact diskJacobi_product_index_infinite A B V

def diskWeakIndex (D : Submodule ℂ ComplexH1) (V : BoundedRealPotential) : ℕ∞ :=
  negativeIndex (fun u : D => (weakJacobi V u u).re)

def pairWeakIndex (D : Submodule ℂ DiskPairH1) (V : BoundedRealPotential) : ℕ∞ :=
  negativeIndex (fun u : finiteH1Domain (pairFiniteDomain D) =>
    (finiteH1Jacobi (pairFiniteDomain D) V u u).re)

lemma pair_reflection_index (D : Submodule ℂ DiskPairH1)
    (A B : Submodule ℂ ComplexH1) [CompleteSpace A] [CompleteSpace B]
    (V : BoundedRealPotential) (e : D ≃ₗ[ℂ] A × B)
    (h : ∀ u v : A × B,
      weakJacobi V (e.symm u).val.1 (e.symm v).val.1 +
      weakJacobi V (e.symm u).val.2 (e.symm v).val.2 =
      2 * (weakJacobi V u.1.val v.1.val + weakJacobi V u.2.val v.2.val)) :
    pairWeakIndex D V = diskWeakIndex A V + diskWeakIndex B V := by
  let f := (pairHilbertCoordinates D).trans e
  let Q : A × B → ℝ := fun u => (weakJacobi V u.1 u.1).re + (weakJacobi V u.2 u.2).re
  have heq (u : finiteH1Domain (pairFiniteDomain D)) :
      (finiteH1Jacobi (pairFiniteDomain D) V u u).re = 2 * Q (f u) := by
    have hh := h (e (pairHilbertCoordinates D u)) (e (pairHilbertCoordinates D u))
    have he := congrArg₂ (fun x y : D =>
      weakJacobi V x.val.1 y.val.1 + weakJacobi V x.val.2 y.val.2)
      (e.symm_apply_apply (pairHilbertCoordinates D u))
      (e.symm_apply_apply (pairHilbertCoordinates D u))
    have hc := (pairFiniteJacobi_eq D V u u).trans (he.symm.trans hh)
    have hre : (2 : ℂ).re = 2 := rfl
    have him : (2 : ℂ).im = 0 := rfl
    simpa only [Complex.mul_re, Complex.add_re, hre, him,
      zero_mul, sub_zero, Q, f, LinearEquiv.trans_apply] using congrArg Complex.re hc
  have hz (C : Submodule ℂ ComplexH1) : (weakJacobi V (0 : C) (0 : C)).re = 0 :=
    congrArg (fun g : C →L[ℂ] ℂ => (g 0).re) ((domainJacobiForm C V).toLinearMap.map_zero)
  have hQ : Q 0 = 0 := (congrArg₂ (fun a b : ℝ => a + b) (hz A) (hz B)).trans (add_zero 0)
  unfold pairWeakIndex
  rw [show (fun u : finiteH1Domain (pairFiniteDomain D) =>
      (finiteH1Jacobi (pairFiniteDomain D) V u u).re) = (fun u => 2 * Q (f u)) from funext heq]
  exact (negativeIndex_pos_mul (fun u => Q (f u)) 2 (by norm_num)).trans
    ((negativeIndex_linearEquiv f Q hQ).trans (diskJacobi_product_index A B V))

lemma paperSlitNeumannCharacter_index (j : ℕ) (V : BoundedRealPotential) :
    pairWeakIndex (paperSlitNeumannCharacterDomain j) V =
      diskWeakIndex (paperHemisphereCharacter j) V + diskWeakIndex (paperNeumannOddCharacter j) V :=
  pair_reflection_index _ _ _ V (paperSlitNeumannCharacterReflectionEquiv j)
    (paperSlitNeumannCharacterReflection_jacobi j V)

lemma paperSlitDirichletCharacter_index (j : ℕ) (V : BoundedRealPotential) :
    pairWeakIndex (paperSlitDirichletCharacterDomain j) V =
      diskWeakIndex (paperDirichletEvenCharacter j) V + diskWeakIndex (paperDirichletOddCharacter j) V :=
  pair_reflection_index _ _ _ V (paperSlitDirichletCharacterReflectionEquiv j)
    (paperSlitDirichletCharacterReflection_jacobi j V)


lemma paperSlitNeumannCharacter_index_mixed (j : ℕ) (V : BoundedRealPotential) :
    pairWeakIndex (paperSlitNeumannCharacterDomain j) V =
      diskWeakIndex (mixedCharacterDomain 3 j true true) V +
      diskWeakIndex (mixedCharacterDomain 3 j false true) V := by
  simpa only [paperHemisphereCharacter_eq_NN, paperNeumannOddCharacter_eq_DN] using
    paperSlitNeumannCharacter_index j V

lemma paperSlitDirichletCharacter_index_mixed (j : ℕ) (V : BoundedRealPotential) :
    pairWeakIndex (paperSlitDirichletCharacterDomain j) V =
      diskWeakIndex (mixedCharacterDomain 3 j true false) V +
      diskWeakIndex (mixedCharacterDomain 3 j false false) V := by
  simpa only [paperDirichletEvenCharacter_eq_ND, paperDirichletOddCharacter_eq_DD] using
    paperSlitDirichletCharacter_index j V

end KsIndex.Spectral
