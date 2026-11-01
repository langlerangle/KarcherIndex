module

public import KsIndexLean.KarcherFixedInfinityGeometry
public import KsIndexLean.KarcherCenteredChartGeometry

@[expose] public section


/-! Exact infinity differential of the same normalized intrinsic immersion. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData

theorem infinity_strip_differential {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (C : PeriodTarget)
    (hC : Continuous (extendedEWMap h.out b C)) (a : ℝ)
    (ha : extendedEWMap h.out b C (infinityParameter k) ∈ (periodProjectionChart a).target) :
    HasFDerivAt (HeightLift.stripAmbient (extendedEWMap h.out b C) a ∘
      (chartAt ℂ (infinityParameter k)).symm) (infinityRealDifferential k 0) 0 := by
  obtain ⟨r, hr0, hr1, X, _, hs, _, hd, he, _⟩ := exists_fixed_infinity_geometry b C hC
  have hb := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr0 : (0 : ℂ) ∈ Metric.ball 0 r)
  have hx : ContDiffAt ℝ ∞ X 0 := hs.contDiffAt hb
  have hg : (extendedEWMap h.out b C ∘ (chartAt ℂ (infinityParameter k)).symm)
      =ᶠ[𝓝 (0 : ℂ)] (fun z => C + projectPeriod (X z)) := by
    filter_upwards [ParameterAtlas.infinity_chart_inverse_germ (k := k), hb] with z hz hzr
    have hq : (chartAt ℂ (infinityParameter k)).symm z =
        infinityParameterChart h.out hr1.le ⟨z, hzr⟩ := Subtype.ext hz
    change extendedEWMap h.out b C _ = _
    rw [hq]
    exact he ⟨z, hzr⟩
  have ht : (extendedEWMap h.out b C ∘ (chartAt ℂ (infinityParameter k)).symm) 0 ∈
      (periodProjectionChart a).target := by
    rw [← ParameterAtlas.parameter_chartAt_infinity (k := k)]
    simpa only [Function.comp_apply, (chartAt ℂ (infinityParameter k)).left_inv
      (mem_chart_source _ _)] using ha
  obtain ⟨hs', hd'⟩ := strip_coordinates_of_local_lift hx hg ht
  have hh := (hs'.differentiableAt (by simp)).hasFDerivAt
  rw [hd', (hd 0 (Metric.mem_ball_self hr0)).fderiv] at hh
  exact hh

theorem lifted_infinity_differential {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (C : PeriodTarget)
    (hC : Continuous (extendedEWMap h.out b C))
    (q : PeriodicEWCarrier h.out b C) (hq : HeightLift.projection q = infinityParameter k) :
    HasFDerivAt (HeightLift.ambient ∘ (HeightLift.liftChart hC q).symm)
      (infinityRealDifferential k 0) 0 := by
  have ha : extendedEWMap h.out b C (infinityParameter k) ∈
      (periodProjectionChart (HeightLift.height q - Real.pi)).target := by
    rw [← hq, ← HeightLift.project_ambient q]
    apply (periodProjectionChart _).map_source
    rw [periodProjectionChart_source]
    exact HeightLift.mem_centered_strip q
  have hd := infinity_strip_differential b C hC (HeightLift.height q - Real.pi) ha
  have he := HeightLift.ambient_chart_germ hC q
  rw [HeightLift.liftChart_apply, hq, ParameterAtlas.parameter_chartAt_infinity] at he
  exact hd.congr_of_eventuallyEq he

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma centeredChart_infinity_differential (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    HasFDerivAt (R.centeredChart q) (infinityRealDifferential k 0) 0 := by
  rw [centeredChart_eq_translate]
  exact (lifted_infinity_differential (reflectionBasepoint k) R.C R.hC q hq).const_add _

lemma normal_eq_centeredChart_infinity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    R.normal q = chartUnitNormal (R.centeredChart q) 0 := by
  rw [infinity_chartUnitNormal_zero h.out (R.centeredChart_infinity_differential q hq)]
  change parameterNormal (HeightLift.projection q) = _
  rw [hq, parameterNormal_infinity]

lemma centeredChart_infinity_metric (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) (d : ℂ) :
    euclideanSq (fderiv ℝ (R.centeredChart q) 0 d) = Surface.rho k 0 ^ 2 * ‖d‖ ^ 2 := by
  rw [(R.centeredChart_infinity_differential q hq).fderiv, infinityRealDifferential_metric h.out]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
