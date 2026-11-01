module

public import KsIndexLean.SphericalSignedForms

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

variable (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
  (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)

def mixedSectorDomain : Submodule ℂ ComplexH1 :=
  mixedTraceDomain k b1 b0 ⊓ weakCharacterDomain θ d

def signedSphereSectorDomain : Submodule ℂ (SphericalSlitNeumannSpace k) :=
  sphericalSignedDomain k b1 b0 ⊓ sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ hθ d

def mixedSectorToSphere (u : mixedSectorDomain k b1 b0 θ d) :
    signedSphereSectorDomain k b1 b0 θ hθ d :=
  ⟨(mixedToSignedSphere k b1 b0 ⟨u.val, u.property.1⟩).val,
    ⟨(mixedToSignedSphere k b1 b0 ⟨u.val, u.property.1⟩).property,
      (mixedSignedSphere_character_iff k b1 b0 θ hθ d ⟨u.val, u.property.1⟩).mpr u.property.2⟩⟩

lemma signedSector_first_mem (q : signedSphereSectorDomain k b1 b0 θ hθ d) :
    (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).1 ∈
      mixedSectorDomain k b1 b0 θ d :=
  ⟨signedSphere_first_mem_mixed k b1 b0 ⟨q.val, q.property.1⟩,
    ((mem_sphereChartCharacterDomain_iff_pair (isOpen_boundaryArc k 1) θ hθ d q.val).mp
      q.property.2).1⟩

def signedSectorToMixed (q : signedSphereSectorDomain k b1 b0 θ hθ d) :
    mixedSectorDomain k b1 b0 θ d :=
  ⟨(sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val).1,
    signedSector_first_mem k b1 b0 θ hθ d q⟩

lemma mixedSectorToSphere_coordinates (u : mixedSectorDomain k b1 b0 θ d) :
    sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1)
      (mixedSectorToSphere k b1 b0 θ hθ d u).val = signedDiskPair b1 u.val :=
  mixedToSignedSphere_coordinates k b1 b0 ⟨u.val, u.property.1⟩

lemma signedSectorToMixed_toSphere (u : mixedSectorDomain k b1 b0 θ d) :
    signedSectorToMixed k b1 b0 θ hθ d (mixedSectorToSphere k b1 b0 θ hθ d u) = u := by
  apply Subtype.ext
  exact congrArg Prod.fst (mixedSectorToSphere_coordinates k b1 b0 θ hθ d u)

lemma mixedSectorToSphere_toMixed (q : signedSphereSectorDomain k b1 b0 θ hθ d) :
    mixedSectorToSphere k b1 b0 θ hθ d (signedSectorToMixed k b1 b0 θ hθ d q) = q := by
  apply Subtype.ext
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  rw [mixedSectorToSphere_coordinates]
  exact Prod.ext rfl ((mem_sphereReflectionDomain_iff k b1 q.val).mp q.property.1.2).symm

lemma mixedSectorToSphere_add (u v : mixedSectorDomain k b1 b0 θ d) :
    mixedSectorToSphere k b1 b0 θ hθ d (u + v) =
      mixedSectorToSphere k b1 b0 θ hθ d u + mixedSectorToSphere k b1 b0 θ hθ d v := by
  apply Subtype.ext
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  change sphereDiskCoordinatesCLM _ (mixedSectorToSphere k b1 b0 θ hθ d (u + v)).val =
    sphereDiskCoordinatesCLM _ ((mixedSectorToSphere k b1 b0 θ hθ d u).val +
      (mixedSectorToSphere k b1 b0 θ hθ d v).val)
  rw [map_add, mixedSectorToSphere_coordinates, mixedSectorToSphere_coordinates,
    mixedSectorToSphere_coordinates]
  exact signedDiskPair_add b1 u.val v.val

lemma mixedSectorToSphere_smul (a : ℂ) (u : mixedSectorDomain k b1 b0 θ d) :
    mixedSectorToSphere k b1 b0 θ hθ d
      ⟨a • u.val, (mixedSectorDomain k b1 b0 θ d).smul_mem a u.property⟩ =
        a • mixedSectorToSphere k b1 b0 θ hθ d u := by
  apply Subtype.ext
  apply sphereDiskCoordinates_injective (isOpen_boundaryArc k 1)
  change sphereDiskCoordinatesCLM _ (mixedSectorToSphere k b1 b0 θ hθ d
    ⟨a • u.val, (mixedSectorDomain k b1 b0 θ d).smul_mem a u.property⟩).val =
      sphereDiskCoordinatesCLM _ (a • (mixedSectorToSphere k b1 b0 θ hθ d u).val)
  rw [map_smul, mixedSectorToSphere_coordinates, mixedSectorToSphere_coordinates]
  exact signedDiskPair_smul b1 a u.val

lemma mixedSectorToSphere_norm (u : mixedSectorDomain k b1 b0 θ d) :
    ‖mixedSectorToSphere k b1 b0 θ hθ d u‖ = ‖u‖ :=
  mixedToSignedSphere_norm k b1 b0 ⟨u.val, u.property.1⟩

def mixedSectorSphereLinearIsometryEquiv :
    mixedSectorDomain k b1 b0 θ d ≃ₗᵢ[ℂ] signedSphereSectorDomain k b1 b0 θ hθ d where
  toFun := mixedSectorToSphere k b1 b0 θ hθ d
  invFun := signedSectorToMixed k b1 b0 θ hθ d
  left_inv := signedSectorToMixed_toSphere k b1 b0 θ hθ d
  right_inv := mixedSectorToSphere_toMixed k b1 b0 θ hθ d
  map_add' := mixedSectorToSphere_add k b1 b0 θ hθ d
  map_smul' := mixedSectorToSphere_smul k b1 b0 θ hθ d
  norm_map' := mixedSectorToSphere_norm k b1 b0 θ hθ d

lemma mixedSectorSphere_jacobi (V : BoundedRealPotential)
    (u v : mixedSectorDomain k b1 b0 θ d) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u).val
      (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d v).val =
        2 * weakJacobi V u.val v.val := by
  change sphereChartJacobi _ V (mixedSectorToSphere k b1 b0 θ hθ d u).val
    (mixedSectorToSphere k b1 b0 θ hθ d v).val = _
  simp only [sphereChartJacobi, mixedSectorToSphere_coordinates, signedDiskPair,
    weakJacobi_unit_smul V (sgn b1) (norm_sgn b1)]
  ring

lemma mixedSectorSphere_dirichlet (u v : mixedSectorDomain k b1 b0 θ d) :
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u).val
      (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d v).val =
        2 * dirichlet u.val v.val := by
  change sphereChartDirichlet _ (mixedSectorToSphere k b1 b0 θ hθ d u).val
    (mixedSectorToSphere k b1 b0 θ hθ d v).val = _
  simp only [sphereChartDirichlet, mixedSectorToSphere_coordinates, signedDiskPair,
    dirichlet_unit_smul (sgn b1) (norm_sgn b1)]
  ring

end KsIndex.Spherical
