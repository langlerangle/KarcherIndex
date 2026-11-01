module

/-
Change of variables for the end chart `σ(ζ) = p + ζ^m`.

The real Jacobian is `m²·‖ζ‖^{2(m−1)}`, the covering weight appearing in
`endPotential`. On any measurable set where the chart is injective, the
nonnegative integral over the image equals the pullback integral with this
weight. The theorem permits an arbitrary nonnegative extended-real integrand.

This is a per-sheet identity; selecting sheets and summing their contributions
are separate steps. Applied to a squared value it gives a weighted integral,
not an unweighted `L²` estimate. Dirichlet-energy transport also uses the
pointwise conformal gradient identity.
-/
public import KsIndexLean.EndChartPotential
public import Mathlib.LinearAlgebra.Complex.Determinant

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart

/-- The end chart at a puncture: `σ(ζ) = p + ζ^m`. -/
def endChart (p : ℂ) (m : ℕ) (ζ : ℂ) : ℂ := p + ζ ^ m

/-- The chart's real-linear derivative: multiplication by `m·ζ^{m−1}`. -/
def endDeriv (m : ℕ) (ζ : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
    ((m : ℂ) * ζ ^ (m - 1))).restrictScalars ℝ

@[simp] lemma endDeriv_apply (m : ℕ) (ζ v : ℂ) :
    endDeriv m ζ v = (m : ℂ) * ζ ^ (m - 1) * v := by
  simp [endDeriv, mul_comm]

/-- The real determinant of complex multiplication is the squared norm (the
holomorphic mirror of `real_det_antilinear`). -/
lemma real_det_linear (J : ℂ →L[ℝ] ℂ) (a : ℂ)
    (h : ∀ v, J v = a * v) : J.toLinearMap.det = ‖a‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, h, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]

/-- The chart has `endDeriv` as its real derivative. -/
lemma hasFDerivAt_endChart (p : ℂ) (m : ℕ) (ζ : ℂ) :
    HasFDerivAt (endChart p m) (endDeriv m ζ) ζ := by
  have h : HasDerivAt (endChart p m) ((m : ℂ) * ζ ^ (m - 1)) ζ :=
    (hasDerivAt_pow m ζ).const_add p
  exact h.hasFDerivAt.restrictScalars ℝ

/-- **The covering Jacobian IS the `endPotential` weight**:
`|det D(σ)| = m²·‖ζ‖^{2(m−1)}`. -/
lemma abs_det_endDeriv (m : ℕ) (ζ : ℂ) :
    |(endDeriv m ζ).toLinearMap.det| = (m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)) := by
  rw [real_det_linear _ ((m : ℂ) * ζ ^ (m - 1)) (endDeriv_apply m ζ)]
  rw [abs_of_nonneg (by positivity)]
  rw [norm_mul, norm_pow, mul_pow, ← pow_mul]
  norm_num [mul_comm]

/-- On a measurable set where the end chart is injective, a nonnegative
integral over its image equals the pullback integral with the covering Jacobian.
Sheet selection and multiplicity sums are not part of this statement. -/
theorem lintegral_endChart_sheet (p : ℂ) (m : ℕ) {S : Set ℂ}
    (hS : MeasurableSet S) (hinj : Set.InjOn (endChart p m) S)
    (F : ℂ → ℝ≥0∞) :
    (∫⁻ w in endChart p m '' S, F w ∂volume)
      = ∫⁻ ζ in S, ENNReal.ofReal ((m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)))
          * F (endChart p m ζ) ∂volume := by
  have hd : ∀ ζ ∈ S, HasFDerivWithinAt (endChart p m) (endDeriv m ζ) S ζ :=
    fun ζ _ => (hasFDerivAt_endChart p m ζ).hasFDerivWithinAt
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hd hinj F
  rw [hh]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with ζ _
  rw [abs_det_endDeriv m ζ]

end KsIndex.EndChart
