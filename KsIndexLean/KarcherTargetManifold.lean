module

public import KsIndexLean.KarcherTargetCharts
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section


/-! Smooth atlas on the actual periodic ambient quotient, with explicit
vertical-strip charts and the existing quotient topology. -/
noncomputable section
open Set
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.PeriodicAmbient

/-- The target's preferred strip is chosen only to contain the given point. -/
def chartIndex (p : PeriodTarget) : ℝ := Classical.choose (periodProjectionChart_cover p)

lemma chartIndex_mem (p : PeriodTarget) :
    p ∈ (periodProjectionChart (chartIndex p)).target :=
  Classical.choose_spec (periodProjectionChart_cover p)

/-- Scope this explicit quotient atlas to avoid changing unrelated chart choices. -/
scoped instance chartedSpace : ChartedSpace AmbientTriple PeriodTarget where
  atlas := Set.range (fun a : ℝ => (periodProjectionChart a).symm)
  chartAt p := (periodProjectionChart (chartIndex p)).symm
  mem_chart_source := chartIndex_mem
  chart_mem_atlas p := ⟨chartIndex p, rfl⟩

/-- Local period translations give the actual quotient a smooth manifold structure. -/
scoped instance smoothManifold : IsManifold 𝓘(ℝ, AmbientTriple) ∞ PeriodTarget := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  intro q hq
  simp only [mfld_simps] at hq ⊢
  exact (periodCoordinateChange_smooth hq.2).1.contDiffWithinAt

/-- Smooth real lifts descend smoothly to the registered periodic manifold,
including arbitrary choices of the integration constant. -/
theorem contMDiffAt_quotient_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : PeriodTarget) {X : E → AmbientTriple} {w : E} (hX : ContDiffAt ℝ ∞ X w) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, AmbientTriple) ∞
      (fun z => C + projectPeriod (X z)) w := by
  obtain ⟨c, rfl⟩ := projectPeriod_surjective C
  have hF : ContDiffAt ℝ ∞ (fun z => c + X z) w := contDiffAt_const.add hX
  have ht := chartIndex_mem (projectPeriod (c + X w))
  have hs := (periodCoordinateChange_smooth ht).1.comp w hF
  rw [contMDiffAt_iff_target]
  constructor
  · exact continuous_const.continuousAt.add
      (continuous_projectPeriod.continuousAt.comp hX.continuousAt)
  · apply ContDiffAt.contMDiffAt
    change ContDiffAt ℝ ∞ (fun z =>
      (periodProjectionChart (chartIndex (projectPeriod c + projectPeriod (X w)))).symm
        (projectPeriod c + projectPeriod (X z))) w
    simpa only [Function.comp_def, projectPeriod_add] using hs

/-- The actual quotient projection is smooth for this atlas. -/
theorem contMDiff_projectPeriod :
    ContMDiff 𝓘(ℝ, AmbientTriple) 𝓘(ℝ, AmbientTriple) ∞ projectPeriod := by
  intro p
  simpa only [zero_add] using
    (contMDiffAt_quotient_lift (0 : PeriodTarget)
      (X := fun q : AmbientTriple => q) (w := p) contDiffAt_id)

end KsIndex.KarcherData.PeriodicAmbient
