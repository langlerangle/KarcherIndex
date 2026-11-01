module

public import KsIndexLean.NamedDomainSpectrum
public import KsIndexLean.ChainChartForms

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Full complex-linear identification between the spectral Hilbert form domain
and the paper's cyclic chart quotient, with the original ZMod copy order. -/
def chainSpectralCoordinates (k m : ℕ) [NeZero m] :
    finiteH1Domain (weakDiskChain k m) ≃ₗ[ℂ] ChainChartSpace k m :=
  (LinearEquiv.ofBijective (finiteH1DomainCoordinates (weakDiskChain k m)).toLinearMap
    (finiteH1DomainCoordinates_bijective (weakDiskChain k m))).trans
      (chainChartLinearIsometryEquiv k m).symm.toLinearEquiv

lemma chainSpectralCoordinates_copy (k m : ℕ) [NeZero m]
    (u : finiteH1Domain (weakDiskChain k m)) :
    chainChartCoordinatesCLM k m (chainSpectralCoordinates k m u) = fun n => u.val n := by
  change ((chainChartLinearIsometryEquiv k m)
    ((chainChartLinearIsometryEquiv k m).symm
      (finiteH1DomainCoordinates (weakDiskChain k m) u))).val = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

lemma chainSpectralCoordinates_jacobi (k m : ℕ) [NeZero m] (V : BoundedRealPotential)
    (u v : finiteH1Domain (weakDiskChain k m)) :
    chainChartJacobi k m V (chainSpectralCoordinates k m u) (chainSpectralCoordinates k m v) =
      finiteH1Jacobi (weakDiskChain k m) V u v := by
  simp only [chainChartJacobi, chainSpectralCoordinates_copy, finiteH1Jacobi]

/-- The spectral mass is the summed weighted chart mass of the quotient's
recovered weak disk functions. -/
lemma chainSpectralCoordinates_mass (k m : ℕ) [NeZero m]
    (u : finiteH1Domain (weakDiskChain k m)) :
    ‖finiteH1WeightedValue (weakDiskChain k m) u‖ ^ 2 =
      ∑ n, ‖weightedDiskValueCLM
        (chainChartCoordinatesCLM k m (chainSpectralCoordinates k m u) n)‖ ^ 2 := by
  rw [chainSpectralCoordinates_copy]
  change ‖weightedFiniteValueCLM (ZMod (2 * m)) (fun n => u.val n)‖ ^ 2 = _
  exact weightedFiniteValueCLM_norm_sq _ _

end KsIndex.Spectral
