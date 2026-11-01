module

public import KsIndexLean.HemisphereWeakDomains
public import KsIndexLean.WeakHemisphereIndex
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


/-! Variational indices of the actual single-hemisphere Jacobi form. -/
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spectral

def hemisphereWeakIndex (k j : ℕ) (b : Bool) : ℕ∞ :=
  NegativeDensity.negativeIndex (fun u : hemisphereCharacterDomain k j b =>
    (hemisphereJacobi (surfacePotential k) u.val u.val).re)

theorem hemisphereWeakIndex_eq_disk (k j : ℕ) (b : Bool) :
    hemisphereWeakIndex k j b =
      diskWeakIndex (mixedCharacterDomain k j b b) (surfacePotential k) := by
  have hz : weakJacobi (surfacePotential k) 0 0 = 0 := by
    simpa only [zero_smul, map_zero, zero_mul] using
      weakJacobi_smul_left (surfacePotential k) (0 : ℂ) 0 0
  have ht := NegativeDensity.negativeIndex_linearEquiv
    (hemisphereDomainEquiv (mixedCharacterDomain k j b b)).symm
    (fun u : mixedCharacterDomain k j b b =>
      (weakJacobi (surfacePotential k) u.val u.val).re)
    (by change (weakJacobi (surfacePotential k) 0 0).re = 0; rw [hz]; rfl)
  unfold hemisphereWeakIndex diskWeakIndex
  simp only [hemisphereJacobi_eq]
  exact ht

theorem hemisphereWeakIndex_eq_seamNat {k : ℕ} (hk : 2 ≤ k) (j : ℕ) (b : Bool) :
    hemisphereWeakIndex k j b = SingleDisk.seamNat k b b j := by
  rw [hemisphereWeakIndex_eq_disk, mixedCharacter_weak_index_eq_seamNat hk]

end KsIndex.Spherical
