module

public import KsIndexLean.KarcherCenteredChartGerm
public import KsIndexLean.KarcherGeometryGerms

@[expose] public section


/-! Minimality and geometric curvature of the actual normalized immersion. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

theorem centeredChart_finite_curvature (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w) :
    chartMeanCurvature (R.centeredChart q) w.val = 0 ∧
      conformalSecondFundamentalNorm (R.centeredChart q) w.val
        (Surface.rho k w.val ^ 2) = Surface.absA k w.val := by
  obtain ⟨r, hr, X, _, hs, _, hd, he, _, hH⟩ :=
    extendedEWMap_finite_local_geometry h.out (reflectionBasepoint k) w R.C
  have hw : w.val ∈ Metric.ball w.val r := Metric.mem_ball_self hr
  have hb := Metric.isOpen_ball.mem_nhds hw
  have hX : ContDiffAt ℝ ∞ X w.val := hs.contDiffAt hb
  have hg : (extendedEWMap h.out (reflectionBasepoint k) R.C ∘
      (chartAt ℂ (finiteParameter w)).symm) =ᶠ[𝓝 w.val]
      (fun z => extendedEWMap h.out (reflectionBasepoint k) R.C (finiteParameter w) +
        projectPeriod (X z)) := by
    filter_upwards [ParameterAtlas.finite_chart_inverse_germ w, hb] with z hz hzr
    let p := (chartAt ℂ (finiteParameter w)).symm z
    have ha : z ∉ Surface.punctures k := by
      intro hzp
      exact p.property ⟨z, hzp, hz.symm⟩
    have hp : finiteParameter (⟨z, ha⟩ : PuncturedPlane k) = p := Subtype.ext hz.symm
    change extendedEWMap h.out (reflectionBasepoint k) R.C p = _
    rw [← hp]
    exact he ⟨z, ha⟩ hzr
  have hX' : ContinuousAt X (R.chartCenter q) := by
    rw [R.chartCenter_finite q w hq]
    exact hX.continuousAt
  have hg' := hg
  rw [← hq, ← R.chartCenter_finite q w hq] at hg'
  obtain ⟨t, ht⟩ := R.centeredChart_germ q X _ hX' hg'
  rw [R.chartCenter_finite q w hq] at ht
  have hopen : IsOpen {z : ℂ | z ∉ Surface.punctures k} :=
    isOpen_ne_fun (continuous_id.pow (2 * k)) continuous_const
  have hnorm := ew_secondFundamentalNorm_eq_absA h.out
    (Metric.isOpen_ball.inter hopen)
    (fun z hz => hz.2) (fun z hz => hd z hz.1) ⟨hw, w.property⟩
    (hX.of_le (by simp) : ContDiffAt ℝ 2 X w.val)
  constructor
  · rw [chartMeanCurvature_germ ht, chartMeanCurvature_translate]
    exact hH w.val hw
  · rw [conformalSecondFundamentalNorm_germ ht, conformalSecondFundamentalNorm_translate]
    exact hnorm

theorem centeredChart_infinity_curvature (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    chartMeanCurvature (R.centeredChart q) 0 = 0 ∧
      conformalSecondFundamentalNorm (R.centeredChart q) 0
        (Surface.rho k 0 ^ 2) = Surface.absA k 0 := by
  obtain ⟨r, hr0, hr1, X, _, hs, _, _, he, hgeo⟩ :=
    exists_fixed_infinity_geometry (reflectionBasepoint k) R.C R.hC
  have hw : (0 : ℂ) ∈ Metric.ball 0 r := Metric.mem_ball_self hr0
  have hb := Metric.isOpen_ball.mem_nhds hw
  have hx : ContDiffAt ℝ ∞ X 0 := hs.contDiffAt hb
  have hg : (extendedEWMap h.out (reflectionBasepoint k) R.C ∘
      (chartAt ℂ (infinityParameter k)).symm) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => R.C + projectPeriod (X z)) := by
    filter_upwards [ParameterAtlas.infinity_chart_inverse_germ (k := k), hb] with z hz hzr
    have hp : (chartAt ℂ (infinityParameter k)).symm z =
        infinityParameterChart h.out hr1.le ⟨z, hzr⟩ := Subtype.ext hz
    change extendedEWMap h.out (reflectionBasepoint k) R.C _ = _
    rw [hp]
    exact he ⟨z, hzr⟩
  have hx' : ContinuousAt X (R.chartCenter q) := by
    rw [R.chartCenter_infinity q hq]
    exact hx.continuousAt
  have hg' := hg
  rw [← hq, ← R.chartCenter_infinity q hq] at hg'
  obtain ⟨t, ht⟩ := R.centeredChart_germ q X R.C hx' hg'
  rw [R.chartCenter_infinity q hq] at ht
  constructor
  · rw [chartMeanCurvature_germ ht, chartMeanCurvature_translate]
    exact (hgeo 0 hw).2.1
  · rw [conformalSecondFundamentalNorm_germ ht, conformalSecondFundamentalNorm_translate]
    exact (hgeo 0 hw).2.2

/-- The actual normalized immersion is minimal everywhere, and its geometric
II norm is the paper's curvature expression in each registered chart. -/
theorem centeredChart_curvature (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    chartMeanCurvature (R.centeredChart q) (R.chartCenter q) = 0 ∧
      conformalSecondFundamentalNorm (R.centeredChart q) (R.chartCenter q)
        (Surface.rho k (R.chartCenter q) ^ 2) = Surface.absA k (R.chartCenter q) := by
  rcases parameterSphere_cases (HeightLift.projection q) with hq | ⟨w, hw⟩
  · rw [R.chartCenter_infinity q hq]
    exact R.centeredChart_infinity_curvature q hq
  · rw [R.chartCenter_finite q w hw.symm]
    exact R.centeredChart_finite_curvature q w hw.symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
