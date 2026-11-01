module

public import KsIndexLean.ChainSpectralCoordinates
public import KsIndexLean.JacobiSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Weighted spherical bulk pairing in the original ordered cyclic charts. -/
def chainChartMass (k m : ℕ) [NeZero m] (u v : ChainChartSpace k m) : ℂ :=
  ∑ n, inner ℂ (weightedDiskValueCLM (chainChartCoordinatesCLM k m u n))
    (weightedDiskValueCLM (chainChartCoordinatesCLM k m v n))

lemma chainSpectralCoordinates_mass_pairing (k m : ℕ) [NeZero m]
    (u v : finiteH1Domain (weakDiskChain k m)) :
    chainChartMass k m (chainSpectralCoordinates k m u) (chainSpectralCoordinates k m v) =
      inner ℂ (finiteH1WeightedValue (weakDiskChain k m) u)
        (finiteH1WeightedValue (weakDiskChain k m) v) := by
  simp only [chainChartMass, chainSpectralCoordinates_copy]
  rfl

/-- The shifted solution-operator eigen-equation is equivalent to the weak Jacobi
equation against every chart test, with parameter `t⁻¹ - (V.C + 1)`.
The equivalence allows the zero vector and does not itself assert an eigenvalue exists. -/
lemma chainSolutionOperator_eigen_iff (k m : ℕ) [NeZero m]
    (V : BoundedRealPotential) (u : ChainChartSpace k m) (t : ℝ) (ht : t ≠ 0) :
    finiteSolutionOperator (weakDiskChain k m) V
        (finiteH1WeightedValue (weakDiskChain k m) ((chainSpectralCoordinates k m).symm u)) =
      (t : ℂ) • finiteH1WeightedValue (weakDiskChain k m)
        ((chainSpectralCoordinates k m).symm u) ↔
    ∀ v : ChainChartSpace k m, chainChartJacobi k m V u v =
      ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) * chainChartMass k m u v := by
  rw [finiteSolutionOperator_eigen_iff _ V _ t ht]
  constructor
  · intro h v
    obtain ⟨x, rfl⟩ := (chainSpectralCoordinates k m).surjective u
    obtain ⟨y, rfl⟩ := (chainSpectralCoordinates k m).surjective v
    simpa only [LinearEquiv.symm_apply_apply, chainSpectralCoordinates_jacobi,
      chainSpectralCoordinates_mass_pairing] using h y
  · intro h v
    have hv := h (chainSpectralCoordinates k m v)
    obtain ⟨x, rfl⟩ := (chainSpectralCoordinates k m).surjective u
    simpa only [LinearEquiv.symm_apply_apply, chainSpectralCoordinates_jacobi,
      chainSpectralCoordinates_mass_pairing] using hv

end KsIndex.Spectral
