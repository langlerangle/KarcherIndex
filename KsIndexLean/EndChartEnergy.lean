module

/-
# Dirichlet energy under an end chart

The chart derivative is multiplication by `m·ζ^{m−1}`. Composition with this
conformal map scales the operator norm exactly by `m‖ζ‖^{m−1}`. Its square
is the covering Jacobian `m²‖ζ‖^{2(m−1)}`, so the change-of-variables formula
absorbs that weight into the energy density of the pullback.

The energy uses the real Fréchet derivative's operator norm, with an arbitrary
real normed codomain. For real-valued fields this norm is the gradient length.
The integral identities apply on a measurable sheet where the chart is
injective; the derivative interpretation additionally uses the chain rule.
The function's squared norm, unlike its derivative energy, retains the
Jacobian weight. Thus the function identity does not provide unweighted L²
control near a degenerate Jacobian. Summation over sheets and unweighted L²
estimates are separate results.
-/
public import KsIndexLean.EndChartTransport

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Exact conformal scaling of the operator norm**: composing with the
chart derivative multiplies the norm by exactly `m‖ζ‖^{m−1}`.  The `≤` is
generic; the `≥` uses that multiplication by a nonzero complex scalar is
invertible with conformal inverse. -/
lemma opNorm_comp_endDeriv (m : ℕ) (ζ : ℂ) (L : ℂ →L[ℝ] F) :
    ‖L.comp (endDeriv m ζ)‖ = (m : ℝ) * ‖ζ‖ ^ (m - 1) * ‖L‖ := by
  have hnorm_a : ‖(m : ℂ) * ζ ^ (m - 1)‖ = (m : ℝ) * ‖ζ‖ ^ (m - 1) := by
    simp [norm_pow]
  rw [← hnorm_a]
  set a : ℂ := (m : ℂ) * ζ ^ (m - 1) with ha
  have hup : ‖L.comp (endDeriv m ζ)‖ ≤ ‖a‖ * ‖L‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [ContinuousLinearMap.comp_apply, endDeriv_apply, ← ha]
    calc ‖L (a * v)‖ ≤ ‖L‖ * ‖a * v‖ := L.le_opNorm _
      _ = ‖a‖ * ‖L‖ * ‖v‖ := by rw [norm_mul]; ring
  refine le_antisymm hup ?_
  rcases eq_or_ne a 0 with h0 | h0
  · simp [h0]
  · have hle : ‖L‖ ≤ ‖L.comp (endDeriv m ζ)‖ * ‖a‖⁻¹ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      have hv : (L.comp (endDeriv m ζ)) (a⁻¹ * v) = L v := by
        rw [ContinuousLinearMap.comp_apply, endDeriv_apply, ← ha, ← mul_assoc,
          mul_inv_cancel₀ h0, one_mul]
      calc ‖L v‖ = ‖(L.comp (endDeriv m ζ)) (a⁻¹ * v)‖ := by rw [hv]
        _ ≤ ‖L.comp (endDeriv m ζ)‖ * ‖a⁻¹ * v‖ :=
            (L.comp (endDeriv m ζ)).le_opNorm _
        _ = ‖L.comp (endDeriv m ζ)‖ * ‖a‖⁻¹ * ‖v‖ := by
            rw [norm_mul, norm_inv]; ring
    calc ‖a‖ * ‖L‖ ≤ ‖a‖ * (‖L.comp (endDeriv m ζ)‖ * ‖a‖⁻¹) :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg a)
      _ = ‖L.comp (endDeriv m ζ)‖ := by
          field_simp

/-- The transported energy density carries exactly the covering weight:
`‖L ∘ Dσ‖² = m²‖ζ‖^{2(m−1)}·‖L‖²` — the SAME factor as `abs_det_endDeriv`. -/
lemma ofReal_sq_comp_endDeriv (m : ℕ) (ζ : ℂ) (L : ℂ →L[ℝ] F) :
    ENNReal.ofReal (‖L.comp (endDeriv m ζ)‖ ^ 2)
      = ENNReal.ofReal ((m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)))
          * ENNReal.ofReal (‖L‖ ^ 2) := by
  rw [opNorm_comp_endDeriv, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow, mul_pow, ← pow_mul]
  norm_num [mul_comm]

/-- The transported integrand IS the composite's derivative: on the sheet,
`ζ ↦ (Du (σ ζ)).comp (endDeriv m ζ)` is the fderiv of `u ∘ σ` (chain rule
with the chart). -/
lemma hasFDerivAt_comp_endChart {u : ℂ → F} {L : ℂ →L[ℝ] F} (p : ℂ) (m : ℕ)
    (ζ : ℂ) (hu : HasFDerivAt u L (endChart p m ζ)) :
    HasFDerivAt (fun z => u (endChart p m z)) (L.comp (endDeriv m ζ)) ζ :=
  hu.comp ζ (hasFDerivAt_endChart p m ζ)

/-- Per-sheet energy transport: the covering Jacobian is absorbed by the
conformal scaling of the energy density.
By `hasFDerivAt_comp_endChart`, when `Du` is the derivative of `u` the
right-hand integrand is the energy density of `u ∘ σ`. -/
theorem lintegral_energy_endChart_sheet (p : ℂ) (m : ℕ) {S : Set ℂ}
    (hS : MeasurableSet S) (hinj : Set.InjOn (endChart p m) S)
    (Du : ℂ → (ℂ →L[ℝ] F)) :
    (∫⁻ w in endChart p m '' S, ENNReal.ofReal (‖Du w‖ ^ 2) ∂volume)
      = ∫⁻ ζ in S,
          ENNReal.ofReal
            (‖(Du (endChart p m ζ)).comp (endDeriv m ζ)‖ ^ 2) ∂volume := by
  rw [lintegral_endChart_sheet p m hS hinj]
  exact lintegral_congr fun ζ =>
    (ofReal_sq_comp_endDeriv m ζ (Du (endChart p m ζ))).symm

omit [NormedSpace ℝ F] in
/-- Per-sheet transport of the function's squared norm retains the covering
Jacobian. This identity does not supply unweighted L² control near points
where that Jacobian degenerates. -/
theorem lintegral_sq_endChart_sheet (p : ℂ) (m : ℕ) {S : Set ℂ}
    (hS : MeasurableSet S) (hinj : Set.InjOn (endChart p m) S) (u : ℂ → F) :
    (∫⁻ w in endChart p m '' S, ENNReal.ofReal (‖u w‖ ^ 2) ∂volume)
      = ∫⁻ ζ in S,
          ENNReal.ofReal ((m : ℝ) ^ 2 * ‖ζ‖ ^ (2 * (m - 1)))
            * ENNReal.ofReal (‖u (endChart p m ζ)‖ ^ 2) ∂volume :=
  lintegral_endChart_sheet p m hS hinj fun w => ENNReal.ofReal (‖u w‖ ^ 2)

end KsIndex.EndChart
