module

public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.RadicalCoordinateTransport
public import KsIndexLean.JacobiRadicalRealization

@[expose] public section


/-! Full-test Jacobi kernels on a single lower hemisphere. -/
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral

/-- The weak kernel in the actual single-hemisphere test domain. -/
def hemisphereWeakRadical (k j : ℕ) (b : Bool) :
    Submodule ℂ (hemisphereCharacterDomain k j b) :=
  @coordinateRadical (mixedCharacterDomain k j b b) (hemisphereCharacterDomain k j b)
    inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedCharacterDomain k j b b) (surfacePotential k))
    (hemisphereDomainEquiv (mixedCharacterDomain k j b b))

/-- This kernel is characterized by the actual spherical integral against
all admissible single-hemisphere test fields. -/
lemma mem_hemisphereWeakRadical (k j : ℕ) (b : Bool) (u : hemisphereCharacterDomain k j b) :
    u ∈ hemisphereWeakRadical k j b ↔
      ∀ v : hemisphereCharacterDomain k j b, hemisphereJacobi (surfacePotential k) u.val v.val = 0 := by
  apply @mem_coordinateRadical (mixedCharacterDomain k j b b) (hemisphereCharacterDomain k j b)
    inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedCharacterDomain k j b b) (surfacePotential k))
    (hemisphereDomainEquiv (mixedCharacterDomain k j b b))
    (fun u v => hemisphereJacobi (surfacePotential k) u.val v.val) _ u
  intro x y
  rw [hemisphereJacobi_eq]
  change weakJacobi (surfacePotential k)
    (hemisphereCoordinates (hemisphereCoordinates.symm x.val))
    (hemisphereCoordinates (hemisphereCoordinates.symm y.val)) = _
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rfl

def hemisphereRadicalEquiv (k j : ℕ) (b : Bool) :
    @formRadical (mixedCharacterDomain k j b b) inferInstance (diskDomain_innerProductSpace _)
      (domainJacobiForm (mixedCharacterDomain k j b b) (surfacePotential k)) ≃ₗ[ℂ]
    hemisphereWeakRadical k j b :=
  @coordinateRadicalEquiv (mixedCharacterDomain k j b b) (hemisphereCharacterDomain k j b)
    inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
    (domainJacobiForm (mixedCharacterDomain k j b b) (surfacePotential k))
    (hemisphereDomainEquiv (mixedCharacterDomain k j b b))

lemma hemisphereWeakRadical_finiteDimensional (k j : ℕ) (b : Bool) :
    FiniteDimensional ℂ (hemisphereWeakRadical k j b) := by
  let := diskRadical_finiteDimensional (mixedCharacterDomain k j b b) (surfacePotential k)
  exact (hemisphereRadicalEquiv k j b).finiteDimensional

end KsIndex.Spherical
