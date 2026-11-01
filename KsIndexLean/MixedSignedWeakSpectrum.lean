module

public import KsIndexLean.NamedDomainSpectrum
public import KsIndexLean.SphericalSignedForms
public import KsIndexLean.JacobiSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.SingleDisk

/-- The summed spherical mass on the reflection-sign sector. -/
def mixedSignedChartMass (k : ℕ) (b1 b0 : Bool)
    (u v : sphericalSignedDomain k b1 b0) : ℂ :=
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) u.val).1)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v.val).1) +
  inner ℂ (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) u.val).2)
    (weightedDiskValueCLM (sphereDiskCoordinatesCLM (isOpen_boundaryArc k 1) v.val).2)

lemma mixedSignedSphere_mass (k : ℕ) (b1 b0 : Bool)
    (u v : mixedTraceDomain k b1 b0) :
    mixedSignedChartMass k b1 b0 (mixedSignedSphereLinearIsometryEquiv k b1 b0 u)
      (mixedSignedSphereLinearIsometryEquiv k b1 b0 v) =
      2 * inner ℂ (weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) u)
        (weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) v) := by
  change mixedSignedChartMass k b1 b0 (mixedToSignedSphere k b1 b0 u)
    (mixedToSignedSphere k b1 b0 v) =
    2 * inner ℂ (weightedDiskValueCLM u.val) (weightedDiskValueCLM v.val)
  simp only [mixedSignedChartMass, mixedToSignedSphere_coordinates, signedDiskPair]
  cases b1 <;> simp [sgn, two_mul]

/-- The two-copy factor cancels in the weak eigenvalue equation for every
choice of mixed boundary signs. -/
lemma mixedSignedSphere_weak_eigen_iff (k : ℕ) (b1 b0 : Bool)
    (V : BoundedRealPotential) (u : mixedTraceDomain k b1 b0) (z : ℂ) :
    (∀ v : sphericalSignedDomain k b1 b0,
      sphereChartJacobi (isOpen_boundaryArc k 1) V
        (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val v.val =
        z * mixedSignedChartMass k b1 b0 (mixedSignedSphereLinearIsometryEquiv k b1 b0 u) v) ↔
    (∀ v : mixedTraceDomain k b1 b0, weakJacobi V u.val v.val =
      z * inner ℂ (weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) u)
        (weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) v)) := by
  constructor
  · intro h v
    have hv := h (mixedSignedSphereLinearIsometryEquiv k b1 b0 v)
    rw [mixedSignedSphere_jacobi k b1 b0 V u v, mixedSignedSphere_mass k b1 b0 u v] at hv
    linear_combination hv / 2
  · intro h v
    obtain ⟨w, rfl⟩ := (mixedSignedSphereLinearIsometryEquiv k b1 b0).surjective v
    rw [mixedSignedSphere_jacobi k b1 b0 V u w, mixedSignedSphere_mass k b1 b0 u w]
    linear_combination 2 * h w

lemma mixedSignedSolutionOperator_eigen_iff (k : ℕ) (b1 b0 : Bool)
    (V : BoundedRealPotential) (u : mixedTraceDomain k b1 b0) (t : ℝ) (ht : t ≠ 0) :
    diskSolutionOperator (mixedTraceDomain k b1 b0) V
        (weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) u) =
      (t : ℂ) • weightedDiskAmbientEmbedding (mixedTraceDomain k b1 b0) u ↔
    ∀ v : sphericalSignedDomain k b1 b0,
      sphereChartJacobi (isOpen_boundaryArc k 1) V
        (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val v.val =
        ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) * mixedSignedChartMass k b1 b0
          (mixedSignedSphereLinearIsometryEquiv k b1 b0 u) v := by
  exact (diskSolutionOperator_eigen_iff (mixedTraceDomain k b1 b0) V u t ht).trans
    (mixedSignedSphere_weak_eigen_iff k b1 b0 V u _).symm

end KsIndex.Spectral
