module

public import KsIndexLean.PaperSectorParameters
public import KsIndexLean.SignedSphereSector
public import KsIndexLean.SmoothReflectionSphere

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

abbrev PaperSignedSphereSector (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool) :=
  signedSphereSectorDomain k b1 b0 (-(2 * Real.pi) / k)
    (circleRotate_boundaryArc_preimage k 1 _ (paperRotation_root k (by omega)))
    (KsIndex.FormIndex.zeta k ^ j)

def paperMixedSectorEquiv (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool) :
    mixedCharacterDomain k j b1 b0 ≃ₗᵢ[ℂ] PaperSignedSphereSector k hk j b1 b0 :=
  mixedSectorSphereLinearIsometryEquiv k b1 b0 _
    (circleRotate_boundaryArc_preimage k 1 _ (paperRotation_root k (by omega))) _

/-- The smooth reflection-character map composed with the spherical sector equivalence. -/
def paperReflectionCharacterToSphere (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool) :
    ↥(SingleCc k b1 b0 ⊓ Erot1 k j) →ₗ[ℂ] PaperSignedSphereSector k hk j b1 b0 :=
  (paperMixedSectorEquiv k hk j b1 b0).toLinearEquiv.toLinearMap.comp
    (reflectionCharacterToMixed hk j b1 b0)

lemma paperReflectionCharacter_coordinates (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool)
    (f : ↥(SingleCc k b1 b0 ⊓ Erot1 k j)) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (paperReflectionCharacterToSphere k hk j b1 b0 f).val =
        signedDiskPair b1 (reflectionCoreH1 hk ⟨f.val, f.property.1⟩) :=
  mixedSectorToSphere_coordinates k b1 b0 _ _ _ (reflectionCharacterToMixed hk j b1 b0 f)

/-- Forgetting the sector recovers `reflectionCoreToSignedSphere`. -/
lemma paperReflectionCharacter_agrees (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool)
    (f : ↥(SingleCc k b1 b0 ⊓ Erot1 k j)) :
    (paperReflectionCharacterToSphere k hk j b1 b0 f).val =
      (reflectionCoreToSignedSphere hk b1 b0 ⟨f.val, f.property.1⟩).val := by
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  rw [paperReflectionCharacter_coordinates, reflectionCoreToSignedSphere_coordinates]

lemma paperReflectionCharacter_chart_ae (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool)
    (f : ↥(SingleCc k b1 b0 ⊓ Erot1 k j)) :
    (fun z => sphereChartValue (isOpen_boundaryArc k 1)
      (paperReflectionCharacterToSphere k hk j b1 b0 f).val (sphereChart z)) =ᵐ[volume]
        SingleDisk.refl (sgn b1) f.val := by
  rw [paperReflectionCharacter_agrees]
  exact reflectionCoreToSignedSphere_chart_ae hk b1 b0 ⟨f.val, f.property.1⟩

lemma paperMixedSector_jacobi (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (b1 b0 : Bool)
    (V : BoundedRealPotential) (u v : mixedCharacterDomain k j b1 b0) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V (paperMixedSectorEquiv k hk j b1 b0 u).val
      (paperMixedSectorEquiv k hk j b1 b0 v).val = 2 * weakJacobi V u.val v.val :=
  mixedSectorSphere_jacobi k b1 b0 _ _ _ V u v

end KsIndex.Spherical
