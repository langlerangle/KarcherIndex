module

public import KsIndexLean.KarcherGlobalFirstGeometry
public import KsIndexLean.KarcherRepresentativeTranslation

@[expose] public section


/-! Transfer of local EW representatives to the actual normalized atlas. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Any local primitive of the fixed EW map agrees with the actual centered
chart representative up to one constant ambient translation. -/
theorem centeredChart_germ (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (X : ℂ → AmbientTriple) (D : PeriodTarget)
    (hX : ContinuousAt X (R.chartCenter q))
    (he : (extendedEWMap h.out (reflectionBasepoint k) R.C ∘
      (chartAt ℂ (HeightLift.projection q)).symm) =ᶠ[𝓝 (R.chartCenter q)]
        (fun z => D + projectPeriod (X z))) :
    ∃ t : AmbientTriple,
      R.centeredChart q =ᶠ[𝓝 (R.chartCenter q)] (fun z => t + X z) := by
  have ha : (extendedEWMap h.out (reflectionBasepoint k) R.C ∘
      (chartAt ℂ (HeightLift.projection q)).symm) (R.chartCenter q) ∈
      (periodProjectionChart (HeightLift.height q - Real.pi)).target := by
    rw [chartCenter, HeightLift.liftChart_apply]
    simp only [Function.comp_apply, (chartAt ℂ (HeightLift.projection q)).left_inv
      (mem_chart_source _ _)]
    rw [← HeightLift.project_ambient q]
    apply (periodProjectionChart _).map_source
    rw [periodProjectionChart_source]
    exact HeightLift.mem_centered_strip q
  obtain ⟨t, ht⟩ := strip_germ_of_local_lift hX he ha
  have hg := HeightLift.ambient_chart_germ R.hC q
  change (HeightLift.ambient ∘ (HeightLift.liftChart R.hC q).symm)
    =ᶠ[𝓝 (R.chartCenter q)] _ at hg
  have hr : (HeightLift.ambient ∘ (HeightLift.liftChart R.hC q).symm)
      =ᶠ[𝓝 (R.chartCenter q)] (fun z => t + X z) := hg.trans ht
  refine ⟨(R.t, (0, Real.pi)) + t, ?_⟩
  rw [centeredChart_eq_translate]
  filter_upwards [hr] with z hz
  rw [hz]
  exact (add_assoc _ _ _).symm

end KsIndex.KarcherData.PaperHalfPeriodRealization
