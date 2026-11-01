module

public import KsIndexLean.MixedSectorWeakSpectrum
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Set
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

lemma mixedSectorChart_negativeIndex_eq_form (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (V : BoundedRealPotential) :
    negativeIndex (fun u : signedSphereSectorDomain k b1 b0 θ hθ d =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) =
    negativeIndex (fun u : mixedSectorDomain k b1 b0 θ d => (weakJacobi V u.val u.val).re) := by
  have hz : (sphereChartJacobi (isOpen_boundaryArc k 1) V
      (0 : signedSphereSectorDomain k b1 b0 θ hθ d).val (0 : signedSphereSectorDomain k b1 b0 θ hθ d).val).re = 0 := by
    have h := sphereChartJacobi_add_left (isOpen_boundaryArc k 1) V 0 0 0
    simp only [add_zero] at h
    have hh : sphereChartJacobi (isOpen_boundaryArc k 1) V 0 0 = 0 := by
      linear_combination -h
    exact congrArg Complex.re hh
  have h := negativeIndex_linearEquiv
    (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d).toLinearEquiv
    (fun u : signedSphereSectorDomain k b1 b0 θ hθ d =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) hz
  have heq : (fun u : mixedSectorDomain k b1 b0 θ d =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V
        (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u).val
        (mixedSectorSphereLinearIsometryEquiv k b1 b0 θ hθ d u).val).re) =
      (fun u => 2 * (weakJacobi V u.val u.val).re) := by
    funext u
    rw [mixedSectorSphere_jacobi]
    simp
  simp only [LinearIsometryEquiv.coe_toLinearEquiv] at h
  rw [heq] at h
  exact h.symm.trans (negativeIndex_pos_mul _ 2 (by norm_num))

lemma mixedSectorChart_negativeIndex_eq_infinite_count (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (V : BoundedRealPotential)
    [Infinite (diskSpectralData (mixedSectorDomain k b1 b0 θ d) V).eigenbasisIndex] :
    negativeIndex (fun u : signedSphereSectorDomain k b1 b0 θ hθ d =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) =
      (diskNegativeCount (mixedSectorDomain k b1 b0 θ d) V : ℕ∞) := by
  rw [mixedSectorChart_negativeIndex_eq_form]
  exact disk_negativeIndex_eq_count (mixedSectorDomain k b1 b0 θ d) V

lemma mixedSectorChart_negativeIndex_eq_finite_count (k : ℕ) (b1 b0 : Bool) (θ : ℝ)
    (hθ : circleRotate θ ⁻¹' boundaryArc k 1 = boundaryArc k 1) (d : ℂ)
    (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedSectorDomain k b1 b0 θ d))] :
    negativeIndex (fun u : signedSphereSectorDomain k b1 b0 θ hθ d =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) =
      ((diskSpectralData (mixedSectorDomain k b1 b0 θ d) V).finiteStrictCount (V.C + 1) 0 : ℕ∞) := by
  rw [mixedSectorChart_negativeIndex_eq_form]
  exact disk_negativeIndex_eq_finite_count (mixedSectorDomain k b1 b0 θ d) V

end KsIndex.Spectral
