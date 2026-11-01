module

public import KsIndexLean.ChainSpectralCoordinates
public import KsIndexLean.IndexCoordinateTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical KsIndex.NegativeDensity

lemma chainChart_negativeIndex_eq_form (k m : ℕ) [NeZero m] (V : BoundedRealPotential) :
    negativeIndex (fun u : ChainChartSpace k m => (chainChartJacobi k m V u u).re) =
      negativeIndex (fun u : finiteH1Domain (weakDiskChain k m) =>
        (finiteH1Jacobi (weakDiskChain k m) V u u).re) := by
  have hz : (chainChartJacobi k m V 0 0).re = 0 := by
    have h := chainChartJacobi_add_left k m V 0 0 0
    simp only [add_zero] at h
    have hh : chainChartJacobi k m V 0 0 = 0 := by linear_combination -h
    rw [hh, Complex.zero_re]
  have h := negativeIndex_linearEquiv (chainSpectralCoordinates k m)
    (fun u => (chainChartJacobi k m V u u).re) hz
  simpa only [chainSpectralCoordinates_jacobi] using h.symm

lemma chainChart_negativeIndex_eq_infinite_count (k m : ℕ) [NeZero m]
    (V : BoundedRealPotential) [Infinite (finiteSpectralData (weakDiskChain k m) V).eigenbasisIndex] :
    negativeIndex (fun u : ChainChartSpace k m => (chainChartJacobi k m V u u).re) =
      (finiteCopyNegativeCount (weakDiskChain k m) V : ℕ∞) := by
  rw [chainChart_negativeIndex_eq_form]
  exact finiteCopy_negativeIndex_eq_count (weakDiskChain k m) V

lemma chainChart_negativeIndex_eq_finite_count (k m : ℕ) [NeZero m]
    (V : BoundedRealPotential) [FiniteDimensional ℂ (WeightedFiniteAmbient (weakDiskChain k m))] :
    negativeIndex (fun u : ChainChartSpace k m => (chainChartJacobi k m V u u).re) =
      ((finiteSpectralData (weakDiskChain k m) V).finiteStrictCount (V.C + 1) 0 : ℕ∞) := by
  rw [chainChart_negativeIndex_eq_form]
  exact finiteCopy_negativeIndex_eq_finite_count (weakDiskChain k m) V

end KsIndex.Spectral
