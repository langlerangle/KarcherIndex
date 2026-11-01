module

public import KsIndexLean.KarcherLiftCharts

@[expose] public section


/-! Actual real ambient representatives in the strip charts of the periodic lift. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
open scoped KsIndex.KarcherData.PeriodicAmbient KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
namespace HeightLift
variable {P : Type*} [TopologicalSpace P] {F : P → PeriodTarget}

/-- Real ambient expression on a height strip; outside its base it is only a
 total extension and no geometric claim is made. -/
def stripAmbient (F : P → PeriodTarget) (a : ℝ) (p : P) : AmbientTriple :=
  (periodProjectionChart a).symm (F p)

/-- The strip expression is the actual ambient map of the inverse strip chart. -/
lemma ambient_strip_inverse (hF : Continuous F) (a : ℝ) (p : stripBase F a) :
    ambient ((stripHomeomorph hF a).symm p).val = stripAmbient F a p.val := rfl

omit [TopologicalSpace P] in
/-- In its strip, the expression recovers the actual ambient point exactly. -/
lemma stripAmbient_projection {a : ℝ} {q : HeightLift F} (hq : q ∈ strip a) :
    stripAmbient F a (projection q) = ambient q := by
  unfold stripAmbient
  rw [← project_ambient q]
  apply periodProjectionChart_inverse
  rw [periodProjectionChart_source]
  exact hq

end HeightLift

/-- Any valid strip inverse preserves the smoothness and differential of an
 actual local EW lift, not merely of one preferred target chart. -/
theorem strip_coordinates_of_local_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → PeriodTarget} {X : E → AmbientTriple} {w : E} {C : PeriodTarget} {a : ℝ}
    (hX : ContDiffAt ℝ ∞ X w)
    (he : f =ᶠ[𝓝 w] (fun z => C + projectPeriod (X z)))
    (ha : f w ∈ (periodProjectionChart a).target) :
    ContDiffAt ℝ ∞ (fun z => (periodProjectionChart a).symm (f z)) w ∧
    fderiv ℝ (fun z => (periodProjectionChart a).symm (f z)) w = fderiv ℝ X w := by
  obtain ⟨c, hc⟩ := projectPeriod_surjective C
  have hw : f w = projectPeriod (c + X w) := by
    rw [projectPeriod_add, hc]
    exact he.self_of_nhds
  have ht : projectPeriod (c + X w) ∈ (periodProjectionChart a).target := hw ▸ ha
  have hs := (periodCoordinateChange_smooth ht).1.comp w (contDiffAt_const.add hX)
  have hd := (periodCoordinateChange_smooth ht).2.comp w
    ((hX.differentiableAt (by simp)).hasFDerivAt.const_add c)
  have he' : (fun z => (periodProjectionChart a).symm (f z)) =ᶠ[𝓝 w]
      (fun z => (periodProjectionChart a).symm (projectPeriod (c + X z))) := by
    filter_upwards [he] with z hz
    rw [hz, projectPeriod_add, hc]
  refine ⟨hs.congr_of_eventuallyEq he', ?_⟩
  rw [he'.fderiv_eq]
  simpa only [ContinuousLinearMap.id_comp, Function.comp_def] using hd.fderiv

/-- Finite parameter charts of the lifted EW map are smooth immersions in every
 valid height strip. The expression is the actual inverse-strip ambient map. -/
theorem finite_strip_immersion {k : ℕ} [h : Fact (2 ≤ k)]
    (b x : PuncturedPlane k) (C : PeriodTarget) (a : ℝ)
    (ha : extendedEWMap h.out b C (finiteParameter x) ∈ (periodProjectionChart a).target) :
    let f := HeightLift.stripAmbient (extendedEWMap h.out b C) a ∘
      (chartAt ℂ (finiteParameter x)).symm
    ContDiffAt ℝ ∞ f (chartAt ℂ (finiteParameter x) (finiteParameter x)) ∧
    Function.Injective (fderiv ℝ f (chartAt ℂ (finiteParameter x) (finiteParameter x))) := by
  obtain ⟨X, hs, he, hi⟩ := finite_chart_lift b x C
  have ht : (extendedEWMap h.out b C ∘ (chartAt ℂ (finiteParameter x)).symm)
      (chartAt ℂ (finiteParameter x) (finiteParameter x)) ∈ (periodProjectionChart a).target := by
    simpa only [Function.comp_apply, (chartAt ℂ (finiteParameter x)).left_inv
      (mem_chart_source _ _)] using ha
  obtain ⟨hs', hd⟩ := strip_coordinates_of_local_lift hs he ht
  exact ⟨hs', hd ▸ hi⟩

/-- One coherent EW extension has smooth, injective real differentials in
 every valid strip at every parameter point, including infinity. -/
theorem exists_continuous_all_strip_immersions {k : ℕ} [h : Fact (2 ≤ k)] (b : PuncturedPlane k) :
    ∃ C : PeriodTarget, Continuous (extendedEWMap h.out b C) ∧
      ∀ p : ParameterSphere k, ∀ a : ℝ,
      extendedEWMap h.out b C p ∈ (periodProjectionChart a).target →
      let f := HeightLift.stripAmbient (extendedEWMap h.out b C) a ∘ (chartAt ℂ p).symm
      ContDiffAt ℝ ∞ f (chartAt ℂ p p) ∧
      Function.Injective (fderiv ℝ f (chartAt ℂ p p)) := by
  obtain ⟨r, hr0, hr1, X, C, hf, he, _, hs, _, hd, hi, _⟩ :=
    exists_extendedEWMap_geometry h.out b
  have hC : Continuous (extendedEWMap h.out b C) := by
    rw [continuous_iff_continuousAt]
    intro p
    rcases parameterSphere_chart_cover h.out hr0 hr1.le p with ⟨w, rfl⟩ | ⟨v, rfl⟩
    · apply (isOpenEmbedding_finiteParameter k).continuousAt_iff.mp
      have hh : extendedEWMap h.out b C ∘ finiteParameter = descendedIntegral h.out b :=
        funext hf
      rw [hh]
      exact (continuous_descendedIntegral h.out b).continuousAt
    · apply (isOpenEmbedding_infinityParameterChart h.out hr1.le).continuousAt_iff.mp
      have hh : extendedEWMap h.out b C ∘ infinityParameterChart h.out hr1.le =
          (fun v : Metric.ball (0 : ℂ) r => C + projectPeriod (X v.val)) := funext he
      rw [hh]
      exact (continuous_const.add (continuous_projectPeriod.comp
        (hs.continuousOn.comp_continuous continuous_subtype_val (fun v => v.property)))).continuousAt
  refine ⟨C, hC, ?_⟩
  intro p a ha
  rcases parameterSphere_cases p with rfl | ⟨w, rfl⟩
  ·
    have hb := Metric.isOpen_ball.mem_nhds
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
    have ht : (extendedEWMap h.out b C ∘ (chartAt ℂ (infinityParameter k)).symm)
        (chartAt ℂ (infinityParameter k) (infinityParameter k)) ∈
        (periodProjectionChart a).target := by
      simpa only [Function.comp_apply, (chartAt ℂ (infinityParameter k)).left_inv
        (mem_chart_source _ _)] using ha
    obtain ⟨hs', hd'⟩ := strip_coordinates_of_local_lift hx hg ht
    exact ⟨hs', hd' ▸ hinj⟩
  · exact finite_strip_immersion b w C a ha

/-- Local immersion statement without the additional continuity witness. -/
theorem exists_all_strip_immersions {k : ℕ} [h : Fact (2 ≤ k)] (b : PuncturedPlane k) :
    ∃ C : PeriodTarget, ∀ p : ParameterSphere k, ∀ a : ℝ,
      extendedEWMap h.out b C p ∈ (periodProjectionChart a).target →
      let f := HeightLift.stripAmbient (extendedEWMap h.out b C) a ∘ (chartAt ℂ p).symm
      ContDiffAt ℝ ∞ f (chartAt ℂ p p) ∧
      Function.Injective (fderiv ℝ f (chartAt ℂ p p)) := by
  obtain ⟨C, _, hC⟩ := exists_continuous_all_strip_immersions b
  exact ⟨C, hC⟩

end KsIndex.KarcherData
