module

public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.RadicalCoordinateTransport
public import KsIndexLean.JacobiRadicalRealization
public import KsIndexLean.HemisphereMixedPunctureRemoval

@[expose] public section


/-! Mixed Jacobi kernels on the lower hemisphere.

The kernel is characterized by the actual spherical Jacobi integral against
all admissible mixed-domain tests. Coordinate transport gives a complex-linear
equivalence with the disk form radical and transfers finite dimensionality.
The two boundary flags also include the pure equal-flag cases.
-/
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral

/-- The mixed weak kernel in the actual single-hemisphere test domain. -/
def hemisphereMixedWeakRadical (k j : ℕ) (b1 b0 : Bool) :
    Submodule ℂ (hemisphereMixedCharacterDomain k j b1 b0) :=
  @coordinateRadical (mixedCharacterDomain k j b1 b0) (hemisphereMixedCharacterDomain k j b1 b0)
    inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedCharacterDomain k j b1 b0) (surfacePotential k))
    (hemisphereDomainEquiv (mixedCharacterDomain k j b1 b0))

/-- This kernel is characterized by the actual spherical integral against all admissible
single-hemisphere mixed test fields. -/
lemma mem_hemisphereMixedWeakRadical (k j : ℕ) (b1 b0 : Bool)
    (u : hemisphereMixedCharacterDomain k j b1 b0) :
    u ∈ hemisphereMixedWeakRadical k j b1 b0 ↔
      ∀ v : hemisphereMixedCharacterDomain k j b1 b0,
        hemisphereJacobi (surfacePotential k) u.val v.val = 0 := by
  apply @mem_coordinateRadical (mixedCharacterDomain k j b1 b0)
    (hemisphereMixedCharacterDomain k j b1 b0)
    inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedCharacterDomain k j b1 b0) (surfacePotential k))
    (hemisphereDomainEquiv (mixedCharacterDomain k j b1 b0))
    (fun u v => hemisphereJacobi (surfacePotential k) u.val v.val) _ u
  intro x y
  rw [hemisphereJacobi_eq]
  change weakJacobi (surfacePotential k)
    (hemisphereCoordinates (hemisphereCoordinates.symm x.val))
    (hemisphereCoordinates (hemisphereCoordinates.symm y.val)) = _
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- `formRadical ≃ hemisphereMixedWeakRadical`: the literal single-hemisphere radical transport. -/
def hemisphereMixedRadicalEquiv (k j : ℕ) (b1 b0 : Bool) :
    @formRadical (mixedCharacterDomain k j b1 b0) inferInstance (diskDomain_innerProductSpace _)
      (domainJacobiForm (mixedCharacterDomain k j b1 b0) (surfacePotential k)) ≃ₗ[ℂ]
    hemisphereMixedWeakRadical k j b1 b0 :=
  @coordinateRadicalEquiv (mixedCharacterDomain k j b1 b0)
    (hemisphereMixedCharacterDomain k j b1 b0)
    inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedCharacterDomain k j b1 b0) (surfacePotential k))
    (hemisphereDomainEquiv (mixedCharacterDomain k j b1 b0))

lemma hemisphereMixedWeakRadical_finiteDimensional (k j : ℕ) (b1 b0 : Bool) :
    FiniteDimensional ℂ (hemisphereMixedWeakRadical k j b1 b0) := by
  let := diskRadical_finiteDimensional (mixedCharacterDomain k j b1 b0) (surfacePotential k)
  exact (hemisphereMixedRadicalEquiv k j b1 b0).finiteDimensional

end KsIndex.Spherical
