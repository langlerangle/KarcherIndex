module

public import KsIndexLean.PureSectorRadicalEquivalence
public import KsIndexLean.PaperSmoothSector
public import KsIndexLean.MixedSectorSpectralNullity

@[expose] public section


/-! Pure bounded-field sectors and the actual signed spherical weak kernels.
The signed sphere has two reflected hemispheres; its form is twice the disk form. -/
noncomputable section
namespace KsIndex.NullityDecomp
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Surface KsIndex.Spectral KsIndex.Spherical

abbrev pureSphereRadical (k : ℕ) (hk : 1 ≤ k) (r s : ℕ) :=
  mixedSectorChartRadical k (decide (s = 0)) (decide (s = 0)) (-(2 * Real.pi) / k)
    (circleRotate_boundaryArc_preimage k 1 _ (paperRotation_root k (by omega)))
    (KsIndex.FormIndex.zeta k ^ r) (surfacePotential k)

/-- The geometric-model sector maps to the full test-kernel of the signed
spherical chart form, not merely to an arbitrary coordinate subspace. -/
def pureSectorSphereRadicalEquiv {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2) :
    boundedJacobiSector k r s s ≃ₗ[ℂ] pureSphereRadical k (by omega) r s :=
  (pureSectorRadicalEquiv hk hs).trans
    (@coordinateRadicalEquiv (mixedCharacterDomain k r (decide (s = 0)) (decide (s = 0)))
      (PaperSignedSphereSector k (by omega) r (decide (s = 0)) (decide (s = 0)))
      inferInstance (diskDomain_innerProductSpace _) inferInstance inferInstance
      (domainJacobiForm _ (surfacePotential k))
      (paperMixedSectorEquiv k (by omega) r (decide (s = 0)) (decide (s = 0))).toLinearEquiv)

lemma pureSphereRadical_iff_tests {k r s : ℕ} (hk : 1 ≤ k)
    (u : PaperSignedSphereSector k hk r (decide (s = 0)) (decide (s = 0))) :
    u ∈ pureSphereRadical k hk r s ↔
      ∀ v : PaperSignedSphereSector k hk r (decide (s = 0)) (decide (s = 0)),
        sphereChartJacobi (isOpen_boundaryArc k 1) (surfacePotential k) u.val v.val = 0 :=
  mem_mixedSectorChartRadical k _ _ _ _ _ _ u

/-- The spherical representative uses exactly the disk restriction already proved. -/
theorem pureSectorSphereRadicalEquiv_coordinates {k r s : ℕ}
    (hk : 2 ≤ k) (hs : s < 2) (W : boundedJacobiSector k r s s) :
    (pureSectorSphereRadicalEquiv hk hs W).val =
      paperMixedSectorEquiv k (by omega) r (decide (s = 0)) (decide (s = 0))
        (pureSectorToRadical hk hs W).val := rfl

/-- The actual spherical kernel and pure bounded sector have the same rank. -/
theorem pure_sector_rank_eq_sphere_radical {k r s : ℕ} (hk : 2 ≤ k) (hs : s < 2) :
    Module.rank ℂ (boundedJacobiSector k r s s) =
      Module.rank ℂ (pureSphereRadical k (by omega) r s) :=
  (pureSectorSphereRadicalEquiv hk hs).rank_eq

end KsIndex.NullityDecomp
