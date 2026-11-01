module

public import KsIndexLean.KarcherLiftGeometry

@[expose] public section


/-! Actual strip representatives differ from EW primitives by locally constant translation. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData

/-- Strengthen differential preservation to equality of germs, so higher
 geometric derivatives can be transferred without assuming their equality. -/
theorem strip_germ_of_local_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → PeriodTarget} {X : E → AmbientTriple} {w : E} {C : PeriodTarget} {a : ℝ}
    (hX : ContinuousAt X w)
    (he : f =ᶠ[𝓝 w] (fun z => C + projectPeriod (X z)))
    (ha : f w ∈ (periodProjectionChart a).target) :
    ∃ t : AmbientTriple,
      (fun z => (periodProjectionChart a).symm (f z)) =ᶠ[𝓝 w] (fun z => t + X z) := by
  obtain ⟨c, hc⟩ := projectPeriod_surjective C
  have hw : f w = projectPeriod (c + X w) := by
    rw [projectPeriod_add, hc]
    exact he.self_of_nhds
  obtain ⟨d, _, hd⟩ := periodCoordinateChange_translation (hw ▸ ha)
  have hg := hd.comp_tendsto (continuousAt_const.add hX).tendsto
  refine ⟨c + d, ?_⟩
  filter_upwards [he, hg] with z hz hgz
  rw [hz, ← hc, ← projectPeriod_add]
  change (periodProjectionChart a).symm (projectPeriod (c + X z)) = _
  change (periodProjectionChart a).symm (projectPeriod (c + X z)) = (c + X z) + d at hgz
  rw [hgz]
  abel

end KsIndex.KarcherData
