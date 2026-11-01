module

public import KsIndexLean.KarcherComplexAtlas
public import Mathlib.Analysis.Calculus.Conformal.NormedSpace

@[expose] public section


/-! Smooth conformal covering coordinates on the same intrinsic EW immersion. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold
namespace KsIndex.KarcherData.HeightLift
variable {P : Type*} [TopologicalSpace P] [ChartedSpace ℂ P]
variable {F : P → PeriodTarget} (hF : Continuous F)

/-- The projection is exactly the identity in the matching lifted/base charts. -/
theorem projection_chart_identity (q : HeightLift F) {z : ℂ}
    (hz : z ∈ (liftChart hF q).target) :
    chartAt ℂ (projection q) (projection ((liftChart hF q).symm z)) = z := by
  rw [liftChart_symm_projection hF hz]
  exact (chartAt ℂ (projection q)).right_inv hz.1

/-- The projection is holomorphic in the existing lifted atlas. -/
theorem projection_contMDiff_complex [IsManifold 𝓘(ℂ, ℂ) ∞ P] :
    let := liftChartedSpace hF
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞ (projection (F := F)) := by
  dsimp only
  let := liftChartedSpace hF
  intro q
  rw [contMDiffAt_iff_source]
  have ht := (liftChart hF q).map_source (liftChart_mem hF q)
  have he : (projection ∘ (liftChart hF q).symm) =ᶠ[𝓝 (liftChart hF q q)]
      (chartAt ℂ (projection q)).symm := by
    filter_upwards [(liftChart hF q).open_target.mem_nhds ht] with z hz
    exact liftChart_symm_projection hF hz
  have hs := (contMDiffOn_chart_symm (I := 𝓘(ℂ, ℂ)) (n := ∞)
    (x := projection q)).contMDiffAt
      ((chartAt ℂ (projection q)).open_target.mem_nhds ht.1)
  have hchart : chartAt ℂ q = liftChart hF q := rfl
  simpa only [mfld_simps, hchart] using (hs.congr_of_eventuallyEq he).contMDiffWithinAt

/-- The coordinate differential is the identity, so it never vanishes. -/
theorem projection_chart_fderiv (q : HeightLift F) {z : ℂ}
    (hz : z ∈ (liftChart hF q).target) :
    fderiv ℂ (chartAt ℂ (projection q) ∘ projection ∘ (liftChart hF q).symm) z =
      ContinuousLinearMap.id ℂ ℂ := by
  have he : (chartAt ℂ (projection q) ∘ projection ∘ (liftChart hF q).symm)
      =ᶠ[𝓝 z] (fun w : ℂ => w) := by
    filter_upwards [(liftChart hF q).open_target.mem_nhds hz] with w hw
    exact projection_chart_identity hF q hw
  rw [he.fderiv_eq]
  exact hasFDerivAt_id z |>.fderiv

/-- Explicit conformality of the covering coordinate expression. -/
theorem projection_chart_conformal (q : HeightLift F) {z : ℂ}
    (hz : z ∈ (liftChart hF q).target) :
    ConformalAt (chartAt ℂ (projection q) ∘ projection ∘ (liftChart hF q).symm) z :=
  (conformalAt_id z).congr hz (liftChart hF q).open_target
    (fun _w hw => projection_chart_identity hF q hw)

end KsIndex.KarcherData.HeightLift

open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The same normalized realization has a holomorphic covering projection;
its local coordinate differential is explicitly identified separately. -/
theorem holomorphic_covering (R : PaperHalfPeriodRealization k) :
    letI := HeightLift.liftChartedSpace R.hC
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞
      (HeightLift.projection (F := extendedEWMap h.out (reflectionBasepoint k) R.C)) ∧
    IsCoveringMap
      (HeightLift.projection (F := extendedEWMap h.out (reflectionBasepoint k) R.C)) := by
  exact ⟨HeightLift.projection_contMDiff_complex R.hC, R.covering⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
