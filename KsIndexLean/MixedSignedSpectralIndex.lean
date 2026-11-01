module

public import KsIndexLean.MixedSignedWeakSpectrum
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

lemma mixedSignedChart_negativeIndex_eq_form (k : ℕ) (b1 b0 : Bool)
    (V : BoundedRealPotential) :
    negativeIndex (fun u : sphericalSignedDomain k b1 b0 =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) =
    negativeIndex (fun u : mixedTraceDomain k b1 b0 => (weakJacobi V u.val u.val).re) := by
  have hz : (sphereChartJacobi (isOpen_boundaryArc k 1) V
      (0 : sphericalSignedDomain k b1 b0).val (0 : sphericalSignedDomain k b1 b0).val).re = 0 := by
    have h := sphereChartJacobi_add_left (isOpen_boundaryArc k 1) V 0 0 0
    simp only [add_zero] at h
    have hh : sphereChartJacobi (isOpen_boundaryArc k 1) V 0 0 = 0 := by
      linear_combination -h
    exact congrArg Complex.re hh
  have h := negativeIndex_linearEquiv
    (mixedSignedSphereLinearIsometryEquiv k b1 b0).toLinearEquiv
    (fun u : sphericalSignedDomain k b1 b0 =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) hz
  have heq : (fun u : mixedTraceDomain k b1 b0 =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V
        (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val
        (mixedSignedSphereLinearIsometryEquiv k b1 b0 u).val).re) =
      (fun u => 2 * (weakJacobi V u.val u.val).re) := by
    funext u
    rw [mixedSignedSphere_jacobi]
    simp
  simp only [LinearIsometryEquiv.coe_toLinearEquiv] at h
  rw [heq] at h
  exact h.symm.trans (negativeIndex_pos_mul _ 2 (by norm_num))

lemma mixedSignedChart_negativeIndex_eq_infinite_count (k : ℕ) (b1 b0 : Bool)
    (V : BoundedRealPotential)
    [Infinite (diskSpectralData (mixedTraceDomain k b1 b0) V).eigenbasisIndex] :
    negativeIndex (fun u : sphericalSignedDomain k b1 b0 =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) =
      (diskNegativeCount (mixedTraceDomain k b1 b0) V : ℕ∞) := by
  rw [mixedSignedChart_negativeIndex_eq_form]
  exact disk_negativeIndex_eq_count (mixedTraceDomain k b1 b0) V

lemma mixedSignedChart_negativeIndex_eq_finite_count (k : ℕ) (b1 b0 : Bool)
    (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedTraceDomain k b1 b0))] :
    negativeIndex (fun u : sphericalSignedDomain k b1 b0 =>
      (sphereChartJacobi (isOpen_boundaryArc k 1) V u.val u.val).re) =
      ((diskSpectralData (mixedTraceDomain k b1 b0) V).finiteStrictCount (V.C + 1) 0 : ℕ∞) := by
  rw [mixedSignedChart_negativeIndex_eq_form]
  exact disk_negativeIndex_eq_finite_count (mixedTraceDomain k b1 b0) V

end KsIndex.Spectral
