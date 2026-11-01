module

public import KsIndexLean.SphericalSignedDomain

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

variable (k : ℕ) (b1 b0 : Bool)

def mixedSignedPair (u : mixedTraceDomain k b1 b0) : slitTraceDomain k (sgn b1 * sgn b0) :=
  ⟨signedDiskPair b1 u.val, (signedDiskPair_mem_slit_iff k b1 b0 u.val).mpr u.property⟩

def mixedToSignedPhase (u : mixedTraceDomain k b1 b0) :
    SphericalSlitPhaseSpace k (sgn b1 * sgn b0) :=
  (slitPhaseLinearIsometryEquiv k (sgn b1 * sgn b0)).symm (mixedSignedPair k b1 b0 u)

lemma mixedToSignedPhase_coordinates (u : mixedTraceDomain k b1 b0) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (mixedToSignedPhase k b1 b0 u).val =
      signedDiskPair b1 u.val := by
  have h := congrArg Subtype.val
    ((slitPhaseLinearIsometryEquiv k (sgn b1 * sgn b0)).apply_symm_apply
      (mixedSignedPair k b1 b0 u))
  exact h

lemma mixedToSignedPhase_reflection (u : mixedTraceDomain k b1 b0) :
    (mixedToSignedPhase k b1 b0 u).val ∈ sphereReflectionDomain k b1 := by
  apply (mem_sphereReflectionDomain_iff k b1 (mixedToSignedPhase k b1 b0 u).val).mpr
  rw [mixedToSignedPhase_coordinates]
  rfl

def mixedToSignedSphere (u : mixedTraceDomain k b1 b0) : sphericalSignedDomain k b1 b0 :=
  ⟨(mixedToSignedPhase k b1 b0 u).val, ⟨(mixedToSignedPhase k b1 b0 u).property,
    mixedToSignedPhase_reflection k b1 b0 u⟩⟩

lemma mixedToSignedSphere_coordinates (u : mixedTraceDomain k b1 b0) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) (mixedToSignedSphere k b1 b0 u).val =
      signedDiskPair b1 u.val := mixedToSignedPhase_coordinates k b1 b0 u

def signedSphereToMixed (q : sphericalSignedDomain k b1 b0) : mixedTraceDomain k b1 b0 :=
  ⟨(sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).1,
    signedSphere_first_mem_mixed k b1 b0 q⟩

lemma signedSphereToMixed_toSphere (u : mixedTraceDomain k b1 b0) :
    signedSphereToMixed k b1 b0 (mixedToSignedSphere k b1 b0 u) = u := by
  apply Subtype.ext
  exact congrArg Prod.fst (mixedToSignedSphere_coordinates k b1 b0 u)

lemma mixedToSignedSphere_toMixed (q : sphericalSignedDomain k b1 b0) :
    mixedToSignedSphere k b1 b0 (signedSphereToMixed k b1 b0 q) = q := by
  apply Subtype.ext
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  rw [mixedToSignedSphere_coordinates]
  exact Prod.ext rfl ((mem_sphereReflectionDomain_iff k b1 q.val).mp q.property.2).symm

lemma mixedToSignedSphere_add (u v : mixedTraceDomain k b1 b0) :
    mixedToSignedSphere k b1 b0 (u + v) =
      mixedToSignedSphere k b1 b0 u + mixedToSignedSphere k b1 b0 v := by
  apply Subtype.ext
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  change sphereDiskCoordinatesCLM _ (mixedToSignedSphere k b1 b0 (u + v)).val =
    sphereDiskCoordinatesCLM _ ((mixedToSignedSphere k b1 b0 u).val +
      (mixedToSignedSphere k b1 b0 v).val)
  rw [map_add, mixedToSignedSphere_coordinates, mixedToSignedSphere_coordinates,
    mixedToSignedSphere_coordinates]
  exact signedDiskPair_add b1 u.val v.val

lemma mixedToSignedSphere_smul (a : ℂ) (u : mixedTraceDomain k b1 b0) :
    mixedToSignedSphere k b1 b0
      ⟨a • u.val, (mixedTraceDomain k b1 b0).smul_mem a u.property⟩ =
        a • mixedToSignedSphere k b1 b0 u := by
  apply Subtype.ext
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  change sphereDiskCoordinatesCLM _ (mixedToSignedSphere k b1 b0
    ⟨a • u.val, (mixedTraceDomain k b1 b0).smul_mem a u.property⟩).val =
      sphereDiskCoordinatesCLM _ (a • (mixedToSignedSphere k b1 b0 u).val)
  rw [map_smul, mixedToSignedSphere_coordinates, mixedToSignedSphere_coordinates]
  exact signedDiskPair_smul b1 a u.val

lemma mixedToSignedSphere_norm (u : mixedTraceDomain k b1 b0) :
    ‖mixedToSignedSphere k b1 b0 u‖ = ‖u‖ := by
  have hn : ‖sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (mixedToSignedSphere k b1 b0 u).val‖ = ‖mixedToSignedSphere k b1 b0 u‖ := rfl
  rw [mixedToSignedSphere_coordinates] at hn
  exact hn.symm.trans (signedDiskPair_norm b1 u.val)

def mixedSignedSphereLinearIsometryEquiv :
    mixedTraceDomain k b1 b0 ≃ₗᵢ[ℂ] sphericalSignedDomain k b1 b0 where
  toFun := mixedToSignedSphere k b1 b0
  invFun := signedSphereToMixed k b1 b0
  left_inv := signedSphereToMixed_toSphere k b1 b0
  right_inv := mixedToSignedSphere_toMixed k b1 b0
  map_add' := mixedToSignedSphere_add k b1 b0
  map_smul' := mixedToSignedSphere_smul k b1 b0
  norm_map' := mixedToSignedSphere_norm k b1 b0

end KsIndex.Spherical
