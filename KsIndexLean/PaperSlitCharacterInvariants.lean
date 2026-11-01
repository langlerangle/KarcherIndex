module

public import KsIndexLean.PaperSlitCharacterCoordinates
public import KsIndexLean.SlitThirdEigenvalue
public import KsIndexLean.RadicalCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

def paperSlitCharacterSpectralCoordinates (α : ℝ) (j : ℕ) :
    finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j)) ≃ₗ[ℂ]
      paperSphericalPhaseCharacter α j :=
  (pairHilbertCoordinates _).trans (paperSlitCharacterSphereEquiv α j)

lemma paperSlitCharacterSpectralCoordinates_jacobi (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential)
    (u v : finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j))) :
    sphereChartJacobi (isOpen_boundaryArc 3 1) V
      (paperSlitCharacterSpectralCoordinates α j u).val.val
      (paperSlitCharacterSpectralCoordinates α j v).val.val =
    finiteH1Jacobi (pairFiniteDomain (paperSlitCharacterDomain α j)) V u v := by
  rw [pairFiniteJacobi_eq]
  exact paperSlitCharacterSphere_jacobi α j V _ _

lemma paperSphericalCharacter_index_eq (α : ℝ) (j : ℕ) (V : BoundedRealPotential) :
    negativeIndex (fun u : paperSphericalPhaseCharacter α j =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val u.val.val).re) =
    pairWeakIndex (paperSlitCharacterDomain α j) V := by
  let Q := fun u : paperSphericalPhaseCharacter α j =>
    (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val u.val.val).re
  have hz : Q 0 = 0 := by
    have h := paperSlitCharacterSpectralCoordinates_jacobi α j V 0 0
    rw [map_zero] at h
    change (sphereChartJacobi _ V _ _).re = 0
    rw [h, ← finiteJacobiForm_apply]
    exact congrArg
      (fun f : finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j)) →L[ℂ] ℂ =>
        (f 0).re)
      ((finiteJacobiForm (pairFiniteDomain (paperSlitCharacterDomain α j)) V).toLinearMap.map_zero)
  have h := negativeIndex_linearEquiv (paperSlitCharacterSpectralCoordinates α j) Q hz
  simpa only [Q, pairWeakIndex, paperSlitCharacterSpectralCoordinates_jacobi] using h.symm

def paperSphericalCharacterRadical (α : ℝ) (j : ℕ) (V : BoundedRealPotential) :
    Submodule ℂ (paperSphericalPhaseCharacter α j) :=
  @coordinateRadical (finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j)))
    (paperSphericalPhaseCharacter α j) inferInstance (finiteH1Domain_innerProductSpace _)
    inferInstance inferInstance (finiteJacobiForm _ V) (paperSlitCharacterSpectralCoordinates α j)

lemma mem_paperSphericalCharacterRadical (α : ℝ) (j : ℕ) (V : BoundedRealPotential)
    (u : paperSphericalPhaseCharacter α j) :
    u ∈ paperSphericalCharacterRadical α j V ↔
      ∀ v : paperSphericalPhaseCharacter α j,
        sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val v.val.val = 0 := by
  apply @mem_coordinateRadical
    (finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j)))
    (paperSphericalPhaseCharacter α j) inferInstance (finiteH1Domain_innerProductSpace _)
    inferInstance inferInstance (finiteJacobiForm _ V) (paperSlitCharacterSpectralCoordinates α j)
    (fun u v => sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val.val v.val.val) _ u
  intro x y
  exact (paperSlitCharacterSpectralCoordinates_jacobi α j V x y).trans
    (finiteJacobiForm_apply _ V x y).symm

lemma paperSphericalCharacterRadical_finrank (α : ℝ) (j : ℕ) (V : BoundedRealPotential) :
    Module.finrank ℂ (paperSphericalCharacterRadical α j V) =
      finiteCopyWeakNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V :=
  @coordinateRadical_finrank
    (finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j)))
    (paperSphericalPhaseCharacter α j) inferInstance (finiteH1Domain_innerProductSpace _)
    inferInstance inferInstance (finiteJacobiForm _ V) (paperSlitCharacterSpectralCoordinates α j)

lemma paperSphericalCharacterRadical_finiteDimensional
    (α : ℝ) (j : ℕ) (V : BoundedRealPotential) :
    FiniteDimensional ℂ (paperSphericalCharacterRadical α j V) := by
  let := finiteCopyRadical_finiteDimensional (pairFiniteDomain (paperSlitCharacterDomain α j)) V
  exact (@coordinateRadicalEquiv
    (finiteH1Domain (pairFiniteDomain (paperSlitCharacterDomain α j)))
    (paperSphericalPhaseCharacter α j) inferInstance (finiteH1Domain_innerProductSpace _)
    inferInstance inferInstance (finiteJacobiForm _ V)
    (paperSlitCharacterSpectralCoordinates α j)).finiteDimensional

lemma three_paperSpherical_zero_index_two {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    negativeIndex (fun u : paperSphericalPhaseCharacter α 0 =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) (surfacePotential 3) u.val.val u.val.val).re) = 2 := by
  rw [paperSphericalCharacter_index_eq]
  exact three_paperSlit_zero_index_two h0 h1

lemma three_paperSpherical_zero_nullity_zero {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    Module.finrank ℂ (paperSphericalCharacterRadical α 0 (surfacePotential 3)) = 0 := by
  rw [paperSphericalCharacterRadical_finrank]
  exact three_paperSlit_zero_nullity_zero h0 h1

lemma three_paperSpherical_index_add_nullity_le_two {α : ℝ}
    (h0 : 0 < α) (h1 : α < 1) {j : ℕ} (hj : j < 3) :
    negativeIndex (fun u : paperSphericalPhaseCharacter α j =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) (surfacePotential 3) u.val.val u.val.val).re) +
    (Module.finrank ℂ (paperSphericalCharacterRadical α j (surfacePotential 3)) : ℕ∞) ≤ 2 := by
  rw [paperSphericalCharacter_index_eq, paperSphericalCharacterRadical_finrank]
  exact three_paperSlit_index_add_nullity_le_two h0 h1 hj

lemma three_paperSpherical_index_ge_one (α : ℝ) {j : ℕ} (hj : j < 3) :
    1 ≤ negativeIndex (fun u : paperSphericalPhaseCharacter α j =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) (surfacePotential 3) u.val.val u.val.val).re) := by
  rw [paperSphericalCharacter_index_eq]
  exact (three_paperSlit_phase_index_bounds α hj).1

end KsIndex.Spectral
