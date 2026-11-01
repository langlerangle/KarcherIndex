module

public import KsIndexLean.KarcherPeriodQuotientManifold

@[expose] public section


/-! Smooth local parameter projections for the EW period quotient atlas. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget} (hF : Continuous F) (m : ℕ)
variable [IsManifold 𝓘(ℝ, ℂ) ∞ P]

lemma quotientProjection_contMDiff :
    letI := periodChartedSpace hF m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (quotientProjection (F := F) m) := by
  letI := periodChartedSpace hF m
  intro q
  rw [contMDiffAt_iff_source]
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    (quotientProjection m ∘ (periodChart hF m q).symm) _ (periodChart hF m q q)
  have ht := (periodChart hF m q).map_source (periodChart_mem hF m q)
  have he : (quotientProjection m ∘ (periodChart hF m q).symm) =ᶠ[𝓝 (periodChart hF m q q)]
      (chartAt ℂ (quotientProjection m q)).symm := by
    filter_upwards [(periodChart hF m q).open_target.mem_nhds ht] with z hz
    exact periodChart_symm_projection hF m hz
  have hb := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞)
    (x := quotientProjection m q)).contMDiffAt
      ((chartAt ℂ (quotientProjection m q)).open_target.mem_nhds
        ((chartAt ℂ (quotientProjection m q)).map_source (mem_chart_source _ _)))
  rw [periodChart_apply] at he ⊢
  exact (hb.congr_of_eventuallyEq he).contMDiffWithinAt

lemma quotientProjection_localInverse_contMDiffAt (q : PeriodQuotient F m) :
    letI := periodChartedSpace hF m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      ((quotientProjection_isLocalHomeomorph hF m).localInverseAt q)
      (quotientProjection m q) := by
  letI := periodChartedSpace hF m
  letI := periodSmoothManifold hF m
  let b := chartAt ℂ (quotientProjection m q)
  have hbp : quotientProjection m q ∈ b.source := mem_chart_source _ _
  have hb := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞)
    (x := quotientProjection m q)).contMDiffAt (b.open_source.mem_nhds hbp)
  have hc := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := q)).contMDiffAt
    ((periodChart hF m q).open_target.mem_nhds
      ((periodChart hF m q).map_source (periodChart_mem hF m q)))
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ((periodChart hF m q).symm) (periodChart hF m q q) at hc
  rw [periodChart_apply] at hc
  have hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      ((periodChart hF m q).symm ∘ b) (quotientProjection m q) := by
    exact hc.comp _ hb
  apply hg.congr_of_eventuallyEq
  filter_upwards [b.open_source.mem_nhds hbp] with p hp
  change (quotientProjection_isLocalHomeomorph hF m).localInverseAt q p =
    (periodChart hF m q).symm (b p)
  change (quotientProjection_isLocalHomeomorph hF m).localInverseAt q p =
    (quotientProjection_isLocalHomeomorph hF m).localInverseAt q (b.symm (b p))
  rw [b.left_inv hp]

/-- Smoothness may be tested in the local EW parameter representation. -/
lemma contMDiffAt_iff_local_parameter
    (f : PeriodQuotient F m → ℂ) (q : PeriodQuotient F m) :
    letI := periodChartedSpace hF m
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f q ↔
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (f ∘ (quotientProjection_isLocalHomeomorph hF m).localInverseAt q)
        (quotientProjection m q) := by
  letI := periodChartedSpace hF m
  constructor
  · intro hf
    have hf' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f
        ((quotientProjection_isLocalHomeomorph hF m).localInverseAt q (quotientProjection m q)) := by
      simpa only [IsLocalHomeomorph.localInverseAt_apply_self] using hf
    exact hf'.comp _ (quotientProjection_localInverse_contMDiffAt hF m q)
  · intro hf
    have hg := hf.comp q (quotientProjection_contMDiff hF m q)
    apply hg.congr_of_eventuallyEq
    let e := (quotientProjection_isLocalHomeomorph hF m).localInverseAt q
    filter_upwards [e.open_target.mem_nhds
      (quotientProjection_isLocalHomeomorph hF m).self_mem_localInverseAt_target] with r hr
    have he : e (quotientProjection m r) = r := by
      simpa only [e, IsLocalHomeomorph.localInverseAt_symm] using e.right_inv hr
    change f r = f (e (quotientProjection m r))
    rw [he]

end KsIndex.KarcherData.HeightLift
