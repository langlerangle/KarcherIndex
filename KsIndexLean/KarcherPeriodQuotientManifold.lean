module

public import KsIndexLean.KarcherPeriodQuotientCharts
public import KsIndexLean.KarcherLiftManifold

@[expose] public section


/-! Smooth structure on the actual period quotient, using its local projection
to the original EW parameter manifold. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget} (hF : Continuous F) (m : ℕ)

def periodChart (q : PeriodQuotient F m) : OpenPartialHomeomorph (PeriodQuotient F m) ℂ :=
  ((quotientProjection_isLocalHomeomorph hF m).localInverseAt q).symm.trans
    (chartAt ℂ (quotientProjection m q))

lemma periodChart_apply (q r : PeriodQuotient F m) : periodChart hF m q r = chartAt ℂ (quotientProjection m q) (quotientProjection m r) := by
  simp [periodChart]

lemma periodChart_mem (q : PeriodQuotient F m) : q ∈ (periodChart hF m q).source := by
  simp [periodChart, mem_chart_source]

/-- Pullback atlas on the existing quotient topology. -/
@[instance_reducible]
def periodChartedSpace : ChartedSpace ℂ (PeriodQuotient F m) where
  atlas := Set.range (periodChart hF m)
  chartAt := periodChart hF m
  mem_chart_source := periodChart_mem hF m
  chart_mem_atlas q := ⟨q, rfl⟩

lemma periodChart_symm_projection {q : PeriodQuotient F m} {z : ℂ}
    (hz : z ∈ (periodChart hF m q).target) :
    quotientProjection m ((periodChart hF m q).symm z) = (chartAt ℂ (quotientProjection m q)).symm z := by
  exact (quotientProjection_isLocalHomeomorph hF m).apply_localInverseAt_of_mem hz.2

lemma periodChart_transition {q r : PeriodQuotient F m} {z : ℂ}
    (hz : z ∈ ((periodChart hF m q).symm.trans (periodChart hF m r)).source) :
    (periodChart hF m r) ((periodChart hF m q).symm z) =
      (chartAt ℂ (quotientProjection m r)) ((chartAt ℂ (quotientProjection m q)).symm z) := by
  rw [periodChart_apply, periodChart_symm_projection hF m hz.1]

/-- Smoothness of the quotient atlas follows from the parameter atlas transitions. -/
theorem periodSmoothManifold [IsManifold 𝓘(ℝ, ℂ) ∞ P] :
    @IsManifold ℝ _ ℂ _ _ ℂ _ 𝓘(ℝ, ℂ) ∞ (PeriodQuotient F m) _ (periodChartedSpace hF m) := by
  let := periodChartedSpace hF m
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨r, rfl⟩ := he'
  intro z hz
  simp only [mfld_simps] at hz ⊢
  have hzq : z ∈ (chartAt ℂ (quotientProjection m q)).target := hz.1.1
  have hzr : (chartAt ℂ (quotientProjection m q)).symm z ∈ (chartAt ℂ (quotientProjection m r)).source := by
    have hr := hz.2.2
    simp only [Set.mem_preimage, OpenPartialHomeomorph.symm_symm,
      IsLocalHomeomorph.localInverseAt_symm] at hr
    rwa [periodChart_symm_projection hF m hz.1] at hr
  have h1 := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := quotientProjection m q)).contMDiffAt
    ((chartAt ℂ (quotientProjection m q)).open_target.mem_nhds hzq)
  have h2 := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := quotientProjection m r)).contMDiffAt
    ((chartAt ℂ (quotientProjection m r)).open_source.mem_nhds hzr)
  have hs := (h2.comp z h1).contDiffAt
  apply hs.contDiffWithinAt.congr
  · intro w hw
    exact periodChart_transition hF m hw
  · exact periodChart_transition hF m hz

end KsIndex.KarcherData.HeightLift
