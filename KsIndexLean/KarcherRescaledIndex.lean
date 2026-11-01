module

public import KsIndexLean.KarcherRescaledDensityGeometry

@[expose] public section


/-! Index of the normalized 1/m-scaled EW immersion in the fixed 2π ambient quotient. -/
noncomputable section
open MeasureTheory
open scoped ENNReal KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open scoped QuotientArea
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Scaling by a nonzero constant preserves exactly the quotient-area null sets.
Thus the preceding almost-everywhere gradient/curvature identifications hold
also for the scaled area measure used in the signed integral. -/
lemma ae_scaledQuotientArea_eq {c : ℝ} (hc : c ≠ 0) :
    ae (R.scaledQuotientArea (m := m) c) = ae R.quotientArea := by
  rw [R.scaledQuotientArea_eq]
  exact Measure.ae_ennreal_smul_measure_eq (by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_ne_zero hc))) _

/-- The fixed-ambient rescaled index. The carrier and its smooth compact test
domain are unchanged; the actual immersion, induced area, gradient density
and curvature density are scaled as proved in the preceding modules. -/
def rescaledIndex : ℕ∞ :=
  FormIndex.formIndex (R.scaledDensityJacobiQ (m := m) (m : ℝ)⁻¹) R.compactSmoothDomain

lemma rescaledIndex_eq_geometricIndex :
    R.rescaledIndex (m := m) = R.geometricIndex (m := m) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  exact R.scaledDensity_formIndex_eq (inv_ne_zero hm)

lemma rescaledIndex_eq_model : R.rescaledIndex (m := m) = Surface.indSurface k m := by
  rw [R.rescaledIndex_eq_geometricIndex, R.geometricIndex_eq_model]

/-- Both invariants are unchanged in the fixed-ambient homothetic formulation. -/
theorem rescaled_invariants_eq :
    R.rescaledIndex (m := m) = R.geometricIndex (m := m) ∧
    R.rescaledNullity (m := m) = R.geometricNullity (m := m) :=
  ⟨R.rescaledIndex_eq_geometricIndex, R.rescaledNullity_eq_geometricNullity⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.ae_scaledQuotientArea_eq
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.rescaledIndex_eq_model
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.rescaled_invariants_eq
