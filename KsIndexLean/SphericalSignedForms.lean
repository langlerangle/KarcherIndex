module

public import KsIndexLean.SphericalSignedEquiv
public import KsIndexLean.PhaseCopyFormSum

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1 KsIndex.SingleDisk

lemma mixedSignedSphere_dirichlet (k : ℕ) (b1 b0 : Bool) (u v : mixedTraceDomain k b1 b0) :
    sphereChartDirichlet (isOpen_boundaryArc k 1)
      (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val
      (mixedSignedSphereLinearIsometryEquiv k b1 b0 v).val = 2 * dirichlet u.val v.val := by
  change sphereChartDirichlet _ (mixedToSignedSphere k b1 b0 u).val
    (mixedToSignedSphere k b1 b0 v).val = _
  simp only [sphereChartDirichlet, mixedToSignedSphere_coordinates, signedDiskPair,
    dirichlet_unit_smul (sgn b1) (norm_sgn b1)]
  ring

lemma mixedSignedSphere_jacobi (k : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential)
    (u v : mixedTraceDomain k b1 b0) :
    sphereChartJacobi (isOpen_boundaryArc k 1) V
      (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val
      (mixedSignedSphereLinearIsometryEquiv k b1 b0 v).val = 2 * weakJacobi V u.val v.val := by
  change sphereChartJacobi _ V (mixedToSignedSphere k b1 b0 u).val
    (mixedToSignedSphere k b1 b0 v).val = _
  simp only [sphereChartJacobi, mixedToSignedSphere_coordinates, signedDiskPair,
    weakJacobi_unit_smul V (sgn b1) (norm_sgn b1)]
  ring

lemma mixedSignedSphere_character_iff (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (u : mixedTraceDomain k b1 b0) :
    (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val ∈
      sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ hθ d ↔
        u.val ∈ weakCharacterDomain θ d := by
  rw [mem_sphereChartCharacterDomain_iff_pair]
  change sphereDiskCoordinatesCLM _ (mixedToSignedSphere k b1 b0 u).val ∈ _ ↔ _
  rw [mixedToSignedSphere_coordinates]
  change (u.val ∈ weakCharacterDomain θ d ∧ sgn b1 • u.val ∈ weakCharacterDomain θ d) ↔ _
  constructor
  · exact And.left
  · intro h
    refine ⟨h, ?_⟩
    rw [mem_weakCharacterDomain, map_smul, (mem_weakCharacterDomain θ d u.val).mp h,
      smul_comm]

end KsIndex.Spherical
