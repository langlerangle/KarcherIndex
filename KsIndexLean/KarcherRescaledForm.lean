module

public import KsIndexLean.KarcherRescaledArea
public import KsIndexLean.KarcherRescaledNullity

@[expose] public section


/-! Cancellation of metric and area scaling in the quotient Jacobi integral. -/
noncomputable section
open MeasureTheory
open scoped ENNReal KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open scoped QuotientArea
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Signed integral of the rescaled coordinate densities against the area
assembled from scaled disk charts. Local geometric identification of the
densities is a separate compatibility statement. -/
def scaledDensityJacobiQ (c : ℝ)
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) : ℝ :=
  ∫ x, ((c ^ 2)⁻¹ * R.quotientGradSq g x -
    (c ^ 2)⁻¹ * R.quotientAbsA x ^ 2 * ‖g x‖ ^ 2) ∂(R.scaledQuotientArea c)

lemma scaledDensityJacobiQ_eq {c : ℝ} (hc : c ≠ 0)
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.scaledDensityJacobiQ c g = R.quotientJacobiQ g := by
  unfold scaledDensityJacobiQ
  rw [R.scaledQuotientArea_eq, integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg c)]
  have he : (fun x => (c ^ 2)⁻¹ * R.quotientGradSq g x -
      (c ^ 2)⁻¹ * R.quotientAbsA x ^ 2 * ‖g x‖ ^ 2) =
      (fun x => (c ^ 2)⁻¹ * (R.quotientGradSq g x - R.quotientAbsA x ^ 2 * ‖g x‖ ^ 2)) := by
    funext x
    ring
  rw [he, integral_const_mul]
  change c ^ 2 * ((c ^ 2)⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc), one_mul]
  rfl

/-- Finite original geometric energies give integrable scaled densities and
an integrable signed form; no convention for divergent integrals is needed. -/
lemma scaledDensity_integrable (c : ℝ)
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (hg : Integrable (R.quotientGradSq g) R.quotientArea)
    (hp : Integrable (fun x => R.quotientAbsA x ^ 2 * ‖g x‖ ^ 2) R.quotientArea) :
    Integrable (fun x => (c ^ 2)⁻¹ * R.quotientGradSq g x -
      (c ^ 2)⁻¹ * R.quotientAbsA x ^ 2 * ‖g x‖ ^ 2) (R.scaledQuotientArea c) := by
  rw [R.scaledQuotientArea_eq]
  have hg' := (hg.const_mul ((c ^ 2)⁻¹)).smul_measure
    (c := ENNReal.ofReal (c ^ 2)) ENNReal.ofReal_ne_top
  have hp' := (hp.const_mul ((c ^ 2)⁻¹)).smul_measure
    (c := ENNReal.ofReal (c ^ 2)) ENNReal.ofReal_ne_top
  have hh := hg'.sub hp'
  change Integrable (fun x => (c ^ 2)⁻¹ * R.quotientGradSq g x -
    (c ^ 2)⁻¹ * (R.quotientAbsA x ^ 2 * ‖g x‖ ^ 2)) _ at hh
  simpa only [mul_assoc] using hh

lemma scaledDensity_formIndex_eq {c : ℝ} (hc : c ≠ 0) :
    FormIndex.formIndex (R.scaledDensityJacobiQ (m := m) c) R.compactSmoothDomain =
      R.geometricIndex (m := m) := by
  have he : R.scaledDensityJacobiQ (m := m) c = R.quotientJacobiQ :=
    funext (R.scaledDensityJacobiQ_eq hc)
  rw [he]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaledDensityJacobiQ_eq
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaledDensity_formIndex_eq

#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaledDensity_integrable
