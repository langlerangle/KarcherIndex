module

public import KsIndexLean.HemisphereMassPairing
public import KsIndexLean.DiskWeakMultiplicity

@[expose] public section


/-! Weak eigenspaces for the lower-hemisphere Jacobi form.

Each transported disk eigenspace is characterized by the actual hemisphere
Jacobi equation against every domain test, using the literal canonical-area
L² mass pairing. The linear equivalence gives equality of multiplicities at
every real eigenvalue. This identifies the spectral problem, beyond equality
of variational indices. The construction is general in the closed disk
submodule `D`, so pure and mixed boundary domains use the same interface.
-/
noncomputable section
open MeasureTheory
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Spectral

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)

/-- The weak eigenspace of the actual lower-hemisphere Jacobi form at level `L`, as the transported
image of the disk eigenspace; characterized by the literal hemisphere eigen-equation in
`mem_hemisphereWeakEigenspace`. -/
def hemisphereWeakEigenspace (L : ℝ) : Submodule ℂ (hemisphereDomain D) :=
  (diskWeakEigenspace D V L).map (hemisphereDomainEquiv D).toLinearMap

/-- **Literal characterization.** Membership is exactly the full-test hemisphere eigen-equation
`hemisphereJacobi V u v = L · (literal lower-hemisphere L² mass of u, v)` against every `v` in the
domain. -/
lemma mem_hemisphereWeakEigenspace (L : ℝ) (u : hemisphereDomain D) :
    u ∈ hemisphereWeakEigenspace D V L ↔
      ∀ v : hemisphereDomain D,
        hemisphereJacobi V u.val v.val = (L : ℂ) * hemisphereMassPairing u.val v.val := by
  have hcoe : ∀ w : hemisphereDomain D,
      ((hemisphereDomainEquiv D).symm w).val = hemisphereCoordinates w.val := fun _ => rfl
  have hcoe2 : ∀ w : D, hemisphereCoordinates ((hemisphereDomainEquiv D) w).val = w.val := fun w =>
    hemisphereCoordinates.apply_symm_apply w.val
  rw [hemisphereWeakEigenspace, Submodule.mem_map_equiv, mem_diskWeakEigenspace_all]
  constructor
  · intro h v
    have ht := h ((hemisphereDomainEquiv D).symm v)
    rw [weightedDiskAmbientEmbedding_inner, hcoe u, hcoe v] at ht
    rw [hemisphereJacobi_eq, hemisphereMassPairing_eq_weightedValue_inner]
    exact ht
  · intro h v'
    have ht := h ((hemisphereDomainEquiv D) v')
    rw [hemisphereJacobi_eq, hemisphereMassPairing_eq_weightedValue_inner, hcoe2 v'] at ht
    rw [weightedDiskAmbientEmbedding_inner, hcoe u]
    exact ht

/-- The disk and actual-hemisphere weak eigenspaces at each level are linearly equivalent. -/
def hemisphereWeakEigenspaceEquiv (L : ℝ) :
    diskWeakEigenspace D V L ≃ₗ[ℂ] hemisphereWeakEigenspace D V L :=
  (diskWeakEigenspace D V L).equivMapOfInjective
    (hemisphereDomainEquiv D).toLinearMap (hemisphereDomainEquiv D).injective

/-- **Multiplicity equality**: the actual hemisphere eigenspace has the same dimension as the disk
eigenspace at every level. -/
lemma hemisphereWeakEigenspace_finrank (L : ℝ) :
    Module.finrank ℂ (hemisphereWeakEigenspace D V L) =
      Module.finrank ℂ (diskWeakEigenspace D V L) :=
  (hemisphereWeakEigenspaceEquiv D V L).finrank_eq.symm

end KsIndex.Spherical
