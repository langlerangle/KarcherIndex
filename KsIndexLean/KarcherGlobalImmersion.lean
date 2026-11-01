module

public import KsIndexLean.KarcherSourceManifold
public import Mathlib.Geometry.Manifold.ImmersionDiff

@[expose] public section


noncomputable section
open Set Topology
open scoped ContDiff Manifold
open scoped KsIndex.KarcherData.PeriodicAmbient KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData

/-- A smooth local lift in the preferred source chart gives manifold smoothness. -/
theorem contMDiffAt_of_chart_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {f : M → PeriodTarget} {p : M} {X : E → AmbientTriple} {C : PeriodTarget}
    (hs : ContDiffAt ℝ ∞ X (chartAt E p p))
    (he : (f ∘ (chartAt E p).symm) =ᶠ[𝓝 (chartAt E p p)]
      (fun z => C + projectPeriod (X z))) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, AmbientTriple) ∞ f p := by
  rw [contMDiffAt_iff_source]
  simpa only [mfld_simps] using
    ((PeriodicAmbient.contMDiffAt_quotient_lift C hs).congr_of_eventuallyEq he).contMDiffWithinAt

/-- A nondegenerate smooth chart lift gives an immersion in the differential sense. -/
theorem isDiffImmersionAt_of_chart_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {f : M → PeriodTarget} {p : M} {X : E → AmbientTriple} {C : PeriodTarget}
    (hs : ContDiffAt ℝ ∞ X (chartAt E p p))
    (he : (f ∘ (chartAt E p).symm) =ᶠ[𝓝 (chartAt E p p)]
      (fun z => C + projectPeriod (X z)))
    (hi : Function.Injective (fderiv ℝ X (chartAt E p p))) :
    IsDiffImmersionAt 𝓘(ℝ, E) 𝓘(ℝ, AmbientTriple) f p := by
  have hm := contMDiffAt_of_chart_lift hs he
  have hd := hm.mdifferentiableAt (by simp)
  obtain ⟨c, hc⟩ := projectPeriod_surjective C
  have hp : f p = projectPeriod (c + X (chartAt E p p)) := by
    have h := he.self_of_nhds
    simpa only [Function.comp_apply, (chartAt E p).left_inv (mem_chart_source _ _),
      projectPeriod_add, hc] using h
  have ht : projectPeriod (c + X (chartAt E p p)) ∈
      (periodProjectionChart (PeriodicAmbient.chartIndex (f p))).target := by
    rw [← hp]; exact PeriodicAmbient.chartIndex_mem _
  have hx := (hs.differentiableAt (by simp)).hasFDerivAt.const_add c
  have hder := (periodCoordinateChange_smooth ht).2.comp (chartAt E p p) hx
  have he' : (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, AmbientTriple) p f) =ᶠ[𝓝 (chartAt E p p)]
      (fun z => (periodProjectionChart (PeriodicAmbient.chartIndex (f p))).symm
        (projectPeriod (c + X z))) := by
    filter_upwards [he] with z hz
    change (periodProjectionChart (PeriodicAmbient.chartIndex (f p))).symm
      (f ((chartAt E p).symm z)) = _
    rw [show f ((chartAt E p).symm z) = C + projectPeriod (X z) from hz,
      projectPeriod_add, hc]
  have heder : fderiv ℝ
      (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, AmbientTriple) p f) (chartAt E p p) =
      fderiv ℝ X (chartAt E p p) := by
    rw [he'.fderiv_eq]
    simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using hder.fderiv
  apply IsDiffImmersionAt.of_injective_of_finiteDimensional
  simp only [mfderiv, ite_eq_left hd, modelWithCornersSelf_coe, Set.range_id,
    fderivWithin_univ]
  rw [show extChartAt 𝓘(ℝ, E) p p = chartAt E p p from rfl, heder]
  exact (tangentSpaceCastModel 𝓘(ℝ, AmbientTriple) (f p)).symm.injective.comp
    (hi.comp (tangentSpaceCastModel 𝓘(ℝ, E) p).injective)

/-- The global finite chart expression is locally the previously integrated EW lift. -/
theorem finite_chart_lift {k : ℕ} [h : Fact (2 ≤ k)]
    (b x : PuncturedPlane k) (C : PeriodTarget) :
    ∃ X : ℂ → AmbientTriple,
      ContDiffAt ℝ ∞ X (chartAt ℂ (finiteParameter x) (finiteParameter x)) ∧
      ((extendedEWMap h.out b C) ∘ (chartAt ℂ (finiteParameter x)).symm)
        =ᶠ[𝓝 (chartAt ℂ (finiteParameter x) (finiteParameter x))]
        (fun z => extendedEWMap h.out b C (finiteParameter x) + projectPeriod (X z)) ∧
      Function.Injective (fderiv ℝ X (chartAt ℂ (finiteParameter x) (finiteParameter x))) := by
  obtain ⟨r, hr, X, _, hs, _, hd, he, hi, _⟩ :=
    extendedEWMap_finite_local_geometry h.out b x C
  rw [ParameterAtlas.parameter_chartAt_finite]
  have hb := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr : x.val ∈ Metric.ball x.val r)
  refine ⟨X, hs.contDiffAt hb, ?_, ?_⟩
  · filter_upwards [ParameterAtlas.finite_chart_inverse_germ x, hb] with z hz hzr
    let q := (chartAt ℂ (finiteParameter x)).symm z
    have ha : z ∉ Surface.punctures k := by
      intro hzp
      exact q.property ⟨z, hzp, hz.symm⟩
    have hq : finiteParameter (⟨z, ha⟩ : PuncturedPlane k) = q := Subtype.ext hz.symm
    change extendedEWMap h.out b C q = _
    rw [← hq]
    exact he ⟨z, ha⟩ hzr
  · rw [(hd _ (Metric.mem_ball_self hr)).fderiv]
    exact hi

/-- The single EW map on the actual punctured sphere is smooth and has an
injective differential everywhere, including the regular infinity point.
No injectivity of its ambient image is asserted. -/
theorem exists_smooth_immersed_extendedEWMap {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) :
    ∃ C : PeriodTarget,
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ (extendedEWMap h.out b C) ∧
      (∀ p : ParameterSphere k,
        IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) (extendedEWMap h.out b C) p) ∧
      (∀ w : PuncturedPlane k,
        extendedEWMap h.out b C (finiteParameter w) = descendedIntegral h.out b w) := by
  obtain ⟨r, hr0, hr1, X, C, hf, he, _, hs, _, hd, hi, _⟩ :=
    exists_extendedEWMap_geometry h.out b
  have hall : ∀ p : ParameterSphere k,
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞ (extendedEWMap h.out b C) p ∧
      IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) (extendedEWMap h.out b C) p := by
    intro p
    rcases parameterSphere_cases p with rfl | ⟨w, rfl⟩
    · have hb := Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self hr0 : (0 : ℂ) ∈ Metric.ball 0 r)
      have hx : ContDiffAt ℝ ∞ X
          (chartAt ℂ (infinityParameter k) (infinityParameter k)) := by
        rw [ParameterAtlas.parameter_chartAt_infinity]
        exact hs.contDiffAt hb
      have hg : ((extendedEWMap h.out b C) ∘ (chartAt ℂ (infinityParameter k)).symm)
          =ᶠ[𝓝 (chartAt ℂ (infinityParameter k) (infinityParameter k))]
          (fun z => C + projectPeriod (X z)) := by
        rw [ParameterAtlas.parameter_chartAt_infinity]
        filter_upwards [ParameterAtlas.infinity_chart_inverse_germ (k := k), hb] with z hz hzr
        have hq : (chartAt ℂ (infinityParameter k)).symm z =
            infinityParameterChart h.out hr1.le ⟨z, hzr⟩ := Subtype.ext hz
        change extendedEWMap h.out b C _ = _
        rw [hq]
        exact he ⟨z, hzr⟩
      have hinj : Function.Injective
          (fderiv ℝ X (chartAt ℂ (infinityParameter k) (infinityParameter k))) := by
        rw [ParameterAtlas.parameter_chartAt_infinity, (hd 0 (Metric.mem_ball_self hr0)).fderiv]
        exact hi 0 (Metric.mem_ball_self hr0)
      exact ⟨contMDiffAt_of_chart_lift hx hg, isDiffImmersionAt_of_chart_lift hx hg hinj⟩
    · obtain ⟨Y, hy, hg, hj⟩ := finite_chart_lift b w C
      exact ⟨contMDiffAt_of_chart_lift hy hg, isDiffImmersionAt_of_chart_lift hy hg hj⟩
  exact ⟨C, fun p => (hall p).1, fun p => (hall p).2, hf⟩

end KsIndex.KarcherData
