module

public import KsIndexLean.KarcherRescaledForm

@[expose] public section


/-! Geometric interpretation of the rescaled quotient densities. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

lemma chartInvMetricGradSq_homothety_total (X : ℂ → AmbientTriple) (w : ℂ)
    {c : ℝ} (hc : c ≠ 0) (f : ℂ → ℂ) :
    chartInvMetricGradSq (c • X) f w = (c ^ 2)⁻¹ * chartInvMetricGradSq X f w := by
  by_cases hX : DifferentiableAt ℝ X w
  · exact chartInvMetricGradSq_homothety hX hc f
  · have hY : ¬ DifferentiableAt ℝ (c • X) w := by
      intro hY
      apply hX
      have he := hY.const_smul c⁻¹
      simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using he
    simp only [chartInvMetricGradSq, chartGramDet, firstFundamentalForm,
      fderiv_zero_of_not_differentiableAt hX, fderiv_zero_of_not_differentiableAt hY]
    simp [euclideanDot]

namespace PaperHalfPeriodRealization
open scoped QuotientArea
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

lemma scaledGradient_ae_geometry {c : ℝ} (hc : c ≠ 0)
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    ∀ᵐ x ∂(R.quotientArea),
      ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k),
        HeightLift.periodQuotientMap m q = x ∧
        ((c ^ 2)⁻¹ * R.quotientGradSq g x = chartInvMetricGradSq (c • R.centeredChart q)
          (g ∘ (HeightLift.periodChart R.hC m x).symm) w.val ∨
         (c ^ 2)⁻¹ * R.quotientGradSq g x = chartInvMetricGradSq
          (c • (centeredLiftAmbient R.C R.t ∘ R.lowerParameterLift q w))
          (fun z => g (HeightLift.periodQuotientMap m (R.lowerParameterLift q w z))) w.val) := by
  filter_upwards [R.quotientGradSq_ae_geometry g] with x hx
  obtain ⟨q,w,hq,hg⟩ := hx
  refine ⟨q,w,hq,?_⟩
  rcases hg with hg | hg
  · exact Or.inl (by rw [chartInvMetricGradSq_homothety_total _ _ hc, hg])
  · exact Or.inr (by rw [chartInvMetricGradSq_homothety_total _ _ hc, hg])

lemma scaledCurvature_ae_geometry {c : ℝ} (hc : c ≠ 0) :
    ∀ᵐ x ∂(R.quotientArea (m := m)),
      ∃ (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (v : PuncturedPlane k),
        HeightLift.periodQuotientMap m q = x ∧ HeightLift.projection q = finiteParameter v ∧
        (c ^ 2)⁻¹ * R.quotientAbsA x ^ 2 =
          conformalSecondFundamentalNormSq (c • R.centeredChart q) v.val
            (chartAreaDensity (c • R.centeredChart q) v.val) := by
  filter_upwards [R.quotientAbsA_ae_geometry (m := m)] with x hx
  obtain ⟨q,v,hq,hp,ha⟩ := hx
  refine ⟨q,v,hq,hp,?_⟩
  have ht : v.val ∈ (HeightLift.liftChart R.hC q).target := by
    rw [← R.chartCenter_finite q v hp]
    exact (HeightLift.liftChart R.hC q).map_source (HeightLift.liftChart_mem R.hC q)
  have hs : ContDiffAt ℝ 2 (R.centeredChart q) v.val :=
    (R.centeredChart_contDiffAt q ht).of_le (by simp)
  rw [chartAreaDensity_homothety (hs.differentiableAt (by norm_num)),
    conformalSecondFundamentalNormSq_homothety hs hc,
    R.centeredChart_areaDensity q v hp, ha, conformalSecondFundamentalNorm_sq]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaledGradient_ae_geometry
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.scaledCurvature_ae_geometry
