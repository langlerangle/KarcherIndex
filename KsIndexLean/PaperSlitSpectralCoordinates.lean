module

public import KsIndexLean.SlitComparisonSpectrum
public import KsIndexLean.SphericalPaperPhase
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

/-- The paper's reciprocal chart-phase convention is handled by its existing
upper/lower sphere equivalence, after the spectral Hilbert coordinate change. -/
def paperSlitSpectralCoordinates (α : ℝ) :
    finiteH1Domain (pairFiniteDomain (paperSlitDomain α)) ≃ₗ[ℂ] PaperSphericalPhaseSpace α :=
  (pairHilbertCoordinates (paperSlitDomain α)).trans
    (paperSlitSphereLinearIsometryEquiv α).toLinearEquiv

lemma paperSlitSpectralCoordinates_jacobi (α : ℝ) (V : BoundedRealPotential)
    (u v : finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) :
    sphereChartJacobi (isOpen_boundaryArc 3 1) V
      (paperSlitSpectralCoordinates α u).val (paperSlitSpectralCoordinates α v).val =
      finiteH1Jacobi (pairFiniteDomain (paperSlitDomain α)) V u v := by
  rw [pairFiniteJacobi_eq]
  exact upperLowerSlitToSphere_jacobi 3 _ (Complex.exp_ne_zero _) V
    (pairHilbertCoordinates (paperSlitDomain α) u) (pairHilbertCoordinates (paperSlitDomain α) v)

lemma paperSlitChart_negativeIndex_eq_form (α : ℝ) (V : BoundedRealPotential) :
    negativeIndex (fun u : PaperSphericalPhaseSpace α =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val u.val).re) =
      negativeIndex (fun u : finiteH1Domain (pairFiniteDomain (paperSlitDomain α)) =>
        (finiteH1Jacobi (pairFiniteDomain (paperSlitDomain α)) V u u).re) := by
  have hz : (sphereChartJacobi (isOpen_boundaryArc 3 1) V
      (0 : PaperSphericalPhaseSpace α).val (0 : PaperSphericalPhaseSpace α).val).re = 0 := by
    have h := paperSlitSpectralCoordinates_jacobi α V 0 0
    rw [map_zero] at h
    rw [h, ← finiteJacobiForm_apply]
    exact congrArg (fun f : finiteH1Domain (pairFiniteDomain (paperSlitDomain α)) →L[ℂ] ℂ =>
      (f 0).re) ((finiteJacobiForm (pairFiniteDomain (paperSlitDomain α)) V).toLinearMap.map_zero)
  have h := negativeIndex_linearEquiv (paperSlitSpectralCoordinates α)
    (fun u : PaperSphericalPhaseSpace α =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val u.val).re) hz
  simpa only [paperSlitSpectralCoordinates_jacobi] using h.symm

instance paperSlitHilbert_complete (α : ℝ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (paperSlitDomain α))) :=
  slitFinite_complete 3 (Complex.exp ((2 * Real.pi * α) * Complex.I))

lemma paperSlitChart_negativeIndex_eq_infinite_count (α : ℝ) (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitDomain α)) V).eigenbasisIndex] :
    negativeIndex (fun u : PaperSphericalPhaseSpace α =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val u.val).re) =
      (finiteCopyNegativeCount (pairFiniteDomain (paperSlitDomain α)) V : ℕ∞) := by
  rw [paperSlitChart_negativeIndex_eq_form]
  exact finiteCopy_negativeIndex_eq_count (pairFiniteDomain (paperSlitDomain α)) V

lemma paperSlitChart_negativeIndex_eq_finite_count (α : ℝ) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitDomain α)))] :
    negativeIndex (fun u : PaperSphericalPhaseSpace α =>
      (sphereChartJacobi (isOpen_boundaryArc 3 1) V u.val u.val).re) =
      ((finiteSpectralData (pairFiniteDomain (paperSlitDomain α)) V).finiteStrictCount (V.C + 1) 0 : ℕ∞) := by
  rw [paperSlitChart_negativeIndex_eq_form]
  exact finiteCopy_negativeIndex_eq_finite_count (pairFiniteDomain (paperSlitDomain α)) V

end KsIndex.Spectral
