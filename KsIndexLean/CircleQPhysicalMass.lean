module

public import KsIndexLean.CircleQEigenvalue
public import KsIndexLean.CircleFourierTransport

@[expose] public section


/-! Coefficient mass and the physical circle L² pairing.
The Fourier convention contributes the factor `(2π)⁻¹`. -/
noncomputable section
open MeasureTheory
namespace KsIndex.Trace

/-- Polarized Parseval in the circle-form mass-pairing notation. -/
theorem coefficient_massPair_eq_normalized_inner (u v : Lp ℂ 2 circleMeasure) :
    Statements.massPair (circleFourierCoeff u) (circleFourierCoeff v) =
      ((2 * Real.pi)⁻¹ : ℝ) • inner ℂ u v := by
  rw [← circleFourierCLE_inner]
  change (∑' n : ℤ, starRingEnd ℂ (circleFourierCoeff u n) * circleFourierCoeff v n) =
    ∑' n : ℤ, inner ℂ (circleFourierCLE u n) (circleFourierCLE v n)
  simp only [circleFourierCLE_apply, RCLike.inner_apply']

end KsIndex.Trace
