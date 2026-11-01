module

/-
KsIndexLean — NonnegSwap: a nonnegative sum/integral interchange on `(0,1]`.

For a `ℤ`-indexed family of nonnegative measurable functions on `Ioc 0 1`: if the lower integral
(over `Ioc 0 1`) of the `ENNReal` sum `∑' ℓ, ENNReal.ofReal (f ℓ ·)` is finite, then each member is
integrable, the integral of the pointwise sum equals the sum of the integrals, and the integrals are
summable.  (Pointwise summability is included in the theorem statement but is not used in its proof.)

Proved by Harmonic's Aristotle from a statement and proof route by Kai.
-/
public import Mathlib

@[expose] public section


noncomputable section

open MeasureTheory Set

namespace KsIndex.NonnegSwap

/-- **Nonnegative sum/integral interchange on `(0,1]`.** -/
theorem integral_Ioc_tsum_of_lintegral_ne_top {f : ℤ → ℝ → ℝ}
    (hmeas : ∀ ℓ, Measurable (f ℓ))
    (hnn : ∀ ℓ, ∀ r ∈ Ioc (0 : ℝ) 1, 0 ≤ f ℓ r)
    (_hsummable : ∀ r ∈ Ioc (0 : ℝ) 1, Summable fun ℓ => f ℓ r)
    (hfin : (∫⁻ r in Ioc (0 : ℝ) 1, ∑' ℓ : ℤ, ENNReal.ofReal (f ℓ r)) ≠ ⊤) :
    (∀ ℓ, IntegrableOn (f ℓ) (Ioc (0 : ℝ) 1))
      ∧ (∫ r in Ioc (0 : ℝ) 1, ∑' ℓ, f ℓ r) = ∑' ℓ, ∫ r in Ioc (0 : ℝ) 1, f ℓ r
      ∧ Summable fun ℓ => ∫ r in Ioc (0 : ℝ) 1, f ℓ r := by
  -- On `Ioc 0 1` the enorm of `f ℓ` is `ENNReal.ofReal (f ℓ ·)`.
  have henorm : ∀ ℓ : ℤ, (∫⁻ r in Ioc (0 : ℝ) 1, ‖f ℓ r‖ₑ)
      = ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f ℓ r) := fun ℓ =>
    setLIntegral_congr_fun measurableSet_Ioc fun r hr => Real.enorm_of_nonneg (hnn ℓ r hr)
  -- The sum of the individual lower integrals is finite.
  have hA : (∑' ℓ : ℤ, ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f ℓ r)) ≠ ⊤ := by
    rw [← lintegral_tsum (f := fun (ℓ : ℤ) (r : ℝ) => ENNReal.ofReal (f ℓ r))
      fun ℓ => (ENNReal.measurable_ofReal.comp (hmeas ℓ)).aemeasurable]
    exact hfin
  have hle : ∀ ℓ : ℤ, (∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f ℓ r))
      ≤ ∑' ℓ : ℤ, ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f ℓ r) := fun ℓ =>
      ENNReal.le_tsum (f := fun j : ℤ =>
        ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f j r)) ℓ
  have hfin' : ∀ ℓ : ℤ, (∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f ℓ r)) ≠ ⊤ := fun ℓ =>
    ne_top_of_le_ne_top hA (hle ℓ)
  have hint : ∀ ℓ, IntegrableOn (f ℓ) (Ioc (0 : ℝ) 1) := by
    intro ℓ
    refine ⟨(hmeas ℓ).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, henorm ℓ]
    exact lt_top_iff_ne_top.mpr (hfin' ℓ)
  refine ⟨hint, ?_, ?_⟩
  · refine integral_tsum (fun ℓ => (hmeas ℓ).aestronglyMeasurable) ?_
    simpa only [henorm] using hA
  · have heq : ∀ ℓ : ℤ, (∫ r in Ioc (0 : ℝ) 1, f ℓ r)
        = (∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal (f ℓ r)).toReal := by
      intro ℓ
      refine integral_eq_lintegral_of_nonneg_ae ?_ (hmeas ℓ).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using hnn ℓ r hr
    simpa only [← heq] using ENNReal.summable_toReal hA

end KsIndex.NonnegSwap
