module

public import KsIndexLean.FullBoundaryMatching
public import KsIndexLean.SphericalPaperPhase
public import KsIndexLean.SphericalPhaseRotation

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.Trace KsIndex.WeakH1

/-- The actual two-chart weak H1 space with the entire equator retained. -/
abbrev UncutSphereSpace := SphereChartSpace Set.univ isOpen_univ

lemma extendedSeamDomain_univ :
    (extendedSeamDomain Set.univ isOpen_univ : Set ℂ) = Metric.ball 0 2 := by
  simp [extendedSeamDomain]

/-- Phase one removes the slit at the level of genuine weak form domains. -/
def zeroPhaseSphereLinearIsometryEquiv {k : ℕ} (hk : 1 ≤ k) :
    SphericalSlitPhaseSpace k 1 ≃ₗᵢ[ℂ] UncutSphereSpace :=
  (slitPhaseLinearIsometryEquiv k 1).trans
    ((LinearIsometryEquiv.ofEq _ _ (slitTraceDomain_one_eq hk)).trans
      (sphereTransmissionLinearIsometryEquiv Set.univ isOpen_univ).symm)

lemma zeroPhaseSphere_coordinates {k : ℕ} (hk : 1 ≤ k)
    (q : SphericalSlitPhaseSpace k 1) :
    sphereDiskCoordinatesCLM isOpen_univ (zeroPhaseSphereLinearIsometryEquiv hk q) =
      sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) q.val := by
  exact congrArg Subtype.val
    ((sphereTransmissionLinearIsometryEquiv Set.univ isOpen_univ).apply_symm_apply
      (LinearIsometryEquiv.ofEq _ _ (slitTraceDomain_one_eq hk)
        (slitPhaseLinearIsometryEquiv k 1 q)))

lemma zeroPhaseSphere_value {k : ℕ} (hk : 1 ≤ k) (q : SphericalSlitPhaseSpace k 1) :
    sphereChartValue isOpen_univ (zeroPhaseSphereLinearIsometryEquiv hk q) =
      sphereChartValue (isOpen_boundaryArc k 1) q.val := by
  change sphereJoinedValue (sphereDiskCoordinatesCLM _ _).1
    (sphereDiskCoordinatesCLM _ _).2 =
      sphereJoinedValue (sphereDiskCoordinatesCLM _ _).1 (sphereDiskCoordinatesCLM _ _).2
  rw [zeroPhaseSphere_coordinates]

lemma zeroPhaseSphere_dirichlet {k : ℕ} (hk : 1 ≤ k) (q r : SphericalSlitPhaseSpace k 1) :
    sphereChartDirichlet isOpen_univ (zeroPhaseSphereLinearIsometryEquiv hk q)
      (zeroPhaseSphereLinearIsometryEquiv hk r) =
        sphereChartDirichlet (isOpen_boundaryArc k 1) q.val r.val := by
  simp only [sphereChartDirichlet, zeroPhaseSphere_coordinates]

lemma zeroPhaseSphere_jacobi {k : ℕ} (hk : 1 ≤ k) (V : BoundedRealPotential)
    (q r : SphericalSlitPhaseSpace k 1) :
    sphereChartJacobi isOpen_univ V (zeroPhaseSphereLinearIsometryEquiv hk q)
      (zeroPhaseSphereLinearIsometryEquiv hk r) =
        sphereChartJacobi (isOpen_boundaryArc k 1) V q.val r.val := by
  simp only [sphereChartJacobi, zeroPhaseSphere_coordinates]

lemma zeroPhaseSphere_character_iff {k : ℕ} (hk : 1 ≤ k) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (q : SphericalSlitPhaseSpace k 1) :
    zeroPhaseSphereLinearIsometryEquiv hk q ∈
      sphereChartCharacterDomain isOpen_univ θ (by simp) d ↔
    q.val ∈ sphereChartCharacterDomain (isOpen_boundaryArc k 1) θ hθ d := by
  exact (mem_sphereChartCharacterDomain_iff_pair isOpen_univ θ (by simp) d
    (zeroPhaseSphereLinearIsometryEquiv hk q)).trans
      ((congrArg (fun p => p ∈ pairCharacterDomain θ d)
        (zeroPhaseSphere_coordinates hk q)).to_iff.trans
        (mem_sphereChartCharacterDomain_iff_pair (isOpen_boundaryArc k 1) θ hθ d q.val).symm)

/-- The paper's alpha = 0 specialization. -/
def paperZeroPhaseSphereLinearIsometryEquiv :
    PaperSphericalPhaseSpace 0 ≃ₗᵢ[ℂ] UncutSphereSpace := by
  unfold PaperSphericalPhaseSpace
  have h : (Complex.exp ((2 * Real.pi * (0 : ℝ)) * Complex.I))⁻¹ = 1 := by simp
  rw [h]
  exact zeroPhaseSphereLinearIsometryEquiv (k := 3) (by omega)

end KsIndex.Spherical
