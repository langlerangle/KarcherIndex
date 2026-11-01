module

public import KsIndexLean.NamedDomainSpectrum
public import KsIndexLean.SignedSphereSector
public import KsIndexLean.JacobiSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Set
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.SingleDisk

instance mixedSectorDomain_complete (k : ℕ) (b1 b0 : Bool) (θ : ℝ) (d : ℂ) :
    CompleteSpace (mixedSectorDomain k b1 b0 θ d) :=
  ((isClosed_mixedTraceDomain k b1 b0).inter (isClosed_weakCharacterDomain θ d)).isComplete.completeSpace_coe

/-- The summed spherical mass on the reflection-sign sector. -/
def mixedSectorChartMass (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (u v : signedSphereSectorDomain k b1 b0 θ hθ d) : ℂ :=
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) u.val).1)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v.val).1) +
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) u.val).2)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v.val).2)

lemma mixedSectorSphere_mass (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (u v : mixedSectorDomain k b1 b0 θ d) :
    mixedSectorChartMass k b1 b0 θ hθ d (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u)
      (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d v) =
      2 * inner ℂ (weightedDiskAmbientEmbedding (mixedSectorDomain k b1 b0 θ d) u)
        (weightedDiskAmbientEmbedding (mixedSectorDomain k b1 b0 θ d) v) := by
  change mixedSectorChartMass k b1 b0 θ hθ d (mixedSectorToSphere k b1 b0 θ hθ d u)
    (mixedSectorToSphere k b1 b0 θ hθ d v) =
    2 * inner ℂ (weightedDiskValueCLM u.val) (weightedDiskValueCLM v.val)
  simp only [mixedSectorChartMass, mixedSectorToSphere_coordinates, signedDiskPair]
  cases b1 <;> simp [sgn, two_mul]

/-- The two-copy factor cancels in the weak eigenvalue equation for every
choice of mixed boundary signs. -/
lemma mixedSectorSphere_weak_eigen_iff (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (V : BoundedRealPotential) (u : mixedSectorDomain k b1 b0 θ d) (z : ℂ) :
    (∀ v : signedSphereSectorDomain k b1 b0 θ hθ d,
      sphereChartJacobi (isOpen_boundaryArc k 1) V
        (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u).val v.val =
        z * mixedSectorChartMass k b1 b0 θ hθ d (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u) v) ↔
    (∀ v : mixedSectorDomain k b1 b0 θ d, weakJacobi V u.val v.val =
      z * inner ℂ (weightedDiskAmbientEmbedding (mixedSectorDomain k b1 b0 θ d) u)
        (weightedDiskAmbientEmbedding (mixedSectorDomain k b1 b0 θ d) v)) := by
  constructor
  · intro h v
    have hv := h (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d v)
    rw [mixedSectorSphere_jacobi k b1 b0 θ hθ d V u v, mixedSectorSphere_mass k b1 b0 θ hθ d u v] at hv
    linear_combination hv / 2
  · intro h v
    obtain ⟨w, rfl⟩ := (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d).surjective v
    rw [mixedSectorSphere_jacobi k b1 b0 θ hθ d V u w, mixedSectorSphere_mass k b1 b0 θ hθ d u w]
    linear_combination 2 * h w

lemma mixedSectorSolutionOperator_eigen_iff (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (V : BoundedRealPotential) (u : mixedSectorDomain k b1 b0 θ d) (t : ℝ) (ht : t ≠ 0) :
    diskSolutionOperator (mixedSectorDomain k b1 b0 θ d) V
        (weightedDiskAmbientEmbedding (mixedSectorDomain k b1 b0 θ d) u) =
      (t : ℂ) • weightedDiskAmbientEmbedding (mixedSectorDomain k b1 b0 θ d) u ↔
    ∀ v : signedSphereSectorDomain k b1 b0 θ hθ d,
      sphereChartJacobi (isOpen_boundaryArc k 1) V
        (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u).val v.val =
        ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) * mixedSectorChartMass k b1 b0 θ hθ d
          (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u) v := by
  exact (diskSolutionOperator_eigen_iff (mixedSectorDomain k b1 b0 θ d) V u t ht).trans
    (mixedSectorSphere_weak_eigen_iff k b1 b0 θ hθ d V u _).symm

end KsIndex.Spectral
