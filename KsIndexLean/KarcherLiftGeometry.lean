module

public import KsIndexLean.KarcherGlobalNormal

@[expose] public section


/-! Exact differentials of the actual lifted immersion in finite source charts. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData

/-- The finite local lift retains its exact EW differential, not just its rank. -/
theorem finite_chart_lift_differential {k : ℕ} [h : Fact (2 ≤ k)]
    (b x : PuncturedPlane k) (C : PeriodTarget) :
    ∃ X : ℂ → AmbientTriple, ContDiffAt ℝ ∞ X x.val ∧
      ((extendedEWMap h.out b C) ∘ (chartAt ℂ (finiteParameter x)).symm)
        =ᶠ[𝓝 x.val]
        (fun z => extendedEWMap h.out b C (finiteParameter x) + projectPeriod (X z)) ∧
      HasFDerivAt X (ewRealDifferential k x.val) x.val := by
  obtain ⟨r, hr, X, _, hs, _, hd, he, _, _⟩ :=
    extendedEWMap_finite_local_geometry h.out b x C
  have hb := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr : x.val ∈ Metric.ball x.val r)
  refine ⟨X, hs.contDiffAt hb, ?_, hd _ (Metric.mem_ball_self hr)⟩
  filter_upwards [ParameterAtlas.finite_chart_inverse_germ x, hb] with z hz hzr
  let q := (chartAt ℂ (finiteParameter x)).symm z
  have ha : z ∉ Surface.punctures k := by
    intro hzp
    exact q.property ⟨z, hzp, hz.symm⟩
  have hq : finiteParameter (⟨z, ha⟩ : PuncturedPlane k) = q := Subtype.ext hz.symm
  change extendedEWMap h.out b C q = _
  rw [← hq]
  exact he ⟨z, ha⟩ hzr

/-- The real inverse-strip expression has the actual finite EW differential. -/
theorem finite_strip_differential {k : ℕ} [h : Fact (2 ≤ k)]
    (b x : PuncturedPlane k) (C : PeriodTarget) (a : ℝ)
    (ha : extendedEWMap h.out b C (finiteParameter x) ∈ (periodProjectionChart a).target) :
    HasFDerivAt (HeightLift.stripAmbient (extendedEWMap h.out b C) a ∘
      (chartAt ℂ (finiteParameter x)).symm) (ewRealDifferential k x.val) x.val := by
  obtain ⟨X, hs, he, hd⟩ := finite_chart_lift_differential b x C
  have ht : (extendedEWMap h.out b C ∘ (chartAt ℂ (finiteParameter x)).symm) x.val ∈
      (periodProjectionChart a).target := by
    rw [← ParameterAtlas.parameter_chartAt_finite x]
    simpa only [Function.comp_apply, (chartAt ℂ (finiteParameter x)).left_inv
      (mem_chart_source _ _)] using ha
  obtain ⟨hs', hd'⟩ := strip_coordinates_of_local_lift hs he ht
  have hh := (hs'.differentiableAt (by simp)).hasFDerivAt
  rw [hd', hd.fderiv] at hh
  exact hh

/-- The raw ambient immersion has the prescribed EW differential in its actual
 lifted finite chart. This conclusion concerns the existing atlas, not a substitute map. -/
theorem lifted_finite_differential {k : ℕ} [h : Fact (2 ≤ k)]
    (b x : PuncturedPlane k) (C : PeriodTarget)
    (hC : Continuous (extendedEWMap h.out b C))
    (q : PeriodicEWCarrier h.out b C) (hq : HeightLift.projection q = finiteParameter x) :
    HasFDerivAt (HeightLift.ambient ∘ (HeightLift.liftChart hC q).symm)
      (ewRealDifferential k x.val) x.val := by
  have ha : extendedEWMap h.out b C (finiteParameter x) ∈
      (periodProjectionChart (HeightLift.height q - Real.pi)).target := by
    rw [← hq, ← HeightLift.project_ambient q]
    apply (periodProjectionChart _).map_source
    rw [periodProjectionChart_source]
    exact HeightLift.mem_centered_strip q
  have hd := finite_strip_differential b x C (HeightLift.height q - Real.pi) ha
  have he := HeightLift.ambient_chart_germ hC q
  rw [HeightLift.liftChart_apply, hq, ParameterAtlas.parameter_chartAt_finite] at he
  exact hd.congr_of_eventuallyEq he

end KsIndex.KarcherData
