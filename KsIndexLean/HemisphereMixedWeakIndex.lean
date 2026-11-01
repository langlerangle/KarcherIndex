module

public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.IndexCoordinateTransport
public import KsIndexLean.HemisphereMixedPunctureRemoval

@[expose] public section


/-! Variational indices of the mixed Jacobi form on the lower hemisphere.

The two boundary flags specify the trace restrictions on the alternating arcs.
Coordinate transport identifies the actual hemisphere index with the disk weak
index, and hence with `seamNat` when `k ≥ 2`. Equal flags include the pure
boundary conditions. Kernel transport is provided separately by
`HemisphereMixedWeakRadical`; eigenvalue multiplicities additionally require
the mass-pairing identification.
-/
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral

/-- The mixed weak variational index in the actual single-hemisphere test domain. -/
def hemisphereMixedWeakIndex (k j : ℕ) (b1 b0 : Bool) : ℕ∞ :=
  NegativeDensity.negativeIndex (fun u : hemisphereMixedCharacterDomain k j b1 b0 =>
    (hemisphereJacobi (surfacePotential k) u.val u.val).re)

theorem hemisphereMixedWeakIndex_eq_disk (k j : ℕ) (b1 b0 : Bool) :
    hemisphereMixedWeakIndex k j b1 b0 =
      diskWeakIndex (mixedCharacterDomain k j b1 b0) (surfacePotential k) := by
  have hz : weakJacobi (surfacePotential k) 0 0 = 0 := by
    have h := weakJacobi_add_left (surfacePotential k) 0 0 0
    simp only [add_zero] at h
    linear_combination -h
  have ht := NegativeDensity.negativeIndex_linearEquiv
    (hemisphereDomainEquiv (mixedCharacterDomain k j b1 b0)).symm
    (fun u : mixedCharacterDomain k j b1 b0 =>
      (weakJacobi (surfacePotential k) u.val u.val).re)
    (by change (weakJacobi (surfacePotential k) 0 0).re = 0; rw [hz]; rfl)
  unfold hemisphereMixedWeakIndex diskWeakIndex
  simp only [hemisphereJacobi_eq]
  exact ht

theorem hemisphereMixedWeakIndex_eq_seamNat {k : ℕ} (hk : 2 ≤ k) (j : ℕ) (b1 b0 : Bool) :
    hemisphereMixedWeakIndex k j b1 b0 = SingleDisk.seamNat k b1 b0 j := by
  rw [hemisphereMixedWeakIndex_eq_disk, mixedCharacter_weak_index_eq_seamNat hk]

end KsIndex.Spherical
