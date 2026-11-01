module

public import KsIndexLean.KarcherQuotientCurvature

@[expose] public section


/-! Integrability and the signed Jacobi integral on the actual EW quotient. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)
  (G : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)

lemma quotientGradSq_nonneg (x : HeightLift.PeriodQuotient
    (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : 0 ≤ R.quotientGradSq G x := by
  unfold quotientGradSq assembleCopyDensity
  apply Finset.sum_nonneg
  intro n _
  by_cases hx : x ∈ R.quotientCopyInterior n
  · rw [Set.indicator_of_mem hx]
    unfold Surface.gradSq
    positivity
  · rw [Set.indicator_of_notMem hx]

lemma compactSmooth_quotient_energy_integrable :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    Integrable (R.quotientGradSq G) R.quotientArea ∧
      Integrable (fun q => R.quotientAbsA q ^ 2 * ‖G q‖ ^ 2) R.quotientArea := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hs hc
  have hf := R.compactSmooth_energy_lt_top G hs hc
  constructor
  · refine ⟨(R.measurable_quotientGradSq G).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (R.quotientGradSq_nonneg G))).mpr ?_⟩
    rw [R.lintegral_quotientGradSq G]
    exact hf.1
  · refine ⟨((R.measurable_quotientAbsA.pow_const 2).mul
        (hs.continuous.measurable.norm.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun q =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)))).mpr ?_⟩
    rw [R.lintegral_quotientPotential G hs.continuous]
    exact hf.2

/-- Signed geometric Jacobi form integrated on the actual period quotient. -/
def quotientJacobiQ : ℝ :=
  ∫ q, (R.quotientGradSq G q - R.quotientAbsA q ^ 2 * ‖G q‖ ^ 2) ∂(R.quotientArea)

lemma compactSmooth_quotientJacobiQ_eq_copywise :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    R.quotientJacobiQ G = ewJacobiQ R G := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hs hc
  have hi := R.compactSmooth_quotient_energy_integrable G hs hc
  rw [quotientJacobiQ, integral_sub hi.1 hi.2,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (R.quotientGradSq_nonneg G))
      hi.1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      hi.2.aestronglyMeasurable,
    R.lintegral_quotientGradSq G, R.lintegral_quotientPotential G hs.continuous]
  rfl

lemma compactSmooth_quotientJacobiQ_eq_model :
    letI := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ G → HasCompactSupport G →
    R.quotientJacobiQ G = Surface.jacobiQ k m (encodeDiskFunction (R.diskFunctionPullback G)) := by
  let := HeightLift.periodChartedSpace R.hC m
  intro hs hc
  rw [R.compactSmooth_quotientJacobiQ_eq_copywise G hs hc,
    R.compactSmooth_ewJacobiQ_eq_model G hs hc]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
