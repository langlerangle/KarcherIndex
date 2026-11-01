module

public import KsIndexLean.KarcherGlobalCurvature

@[expose] public section


/-! Coordinate overlap identities for the same actual normalized immersion. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

theorem centeredChart_contDiffAt (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ (HeightLift.liftChart R.hC q).target) :
    ContDiffAt ℝ ∞ (R.centeredChart q) z := by
  let := HeightLift.liftChartedSpace R.hC
  let := R.geometry.1
  have hi := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := q)).contMDiffAt
    ((HeightLift.liftChart R.hC q).open_target.mem_nhds hz)
  exact (R.centered_geometry.1.contMDiffAt.comp z hi).contDiffAt

theorem centeredChart_overlap_germ (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) :
    R.centeredChart q =ᶠ[𝓝 z]
      (R.centeredChart r ∘ (HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm)) := by
  filter_upwards [((HeightLift.liftChart R.hC q).symm.trans
    (HeightLift.liftChart R.hC r)).open_source.mem_nhds hz] with w hw
  exact congrArg (centeredLiftAmbient R.C R.t)
    ((HeightLift.liftChart R.hC r).left_inv hw.2).symm

theorem chartTransition_contDiffAt (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) :
    ContDiffAt ℝ ∞ (HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm) z := by
  let := HeightLift.liftChartedSpace R.hC
  let := R.geometry.1
  have hi := (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := q)).contMDiffAt
    ((HeightLift.liftChart R.hC q).open_target.mem_nhds hz.1)
  have hj := (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ∞) (x := r)).contMDiffAt
    ((HeightLift.liftChart R.hC r).open_source.mem_nhds hz.2)
  exact (hj.comp z hi).contDiffAt

/-- The actual first fundamental form transforms in both covariant slots on
every registered chart overlap, with the actual transition derivative. -/
theorem firstFundamentalForm_chart_overlap (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) (a b : ℂ) :
    let c := HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm
    firstFundamentalForm (R.centeredChart q) z a b =
      firstFundamentalForm (R.centeredChart r) (c z)
        (fderiv ℝ c z a) (fderiv ℝ c z b) := by
  dsimp only
  have ht := (HeightLift.liftChart R.hC r).map_source hz.2
  have hd := (R.centeredChart_contDiffAt r ht).differentiableAt (by simp)
  have hc := (R.chartTransition_contDiffAt q r hz).differentiableAt (by simp)
  have he := R.centeredChart_overlap_germ q r hz
  simp only [firstFundamentalForm, he.fderiv_eq, fderiv_comp z hd hc,
    ContinuousLinearMap.comp_apply]

end KsIndex.KarcherData.PaperHalfPeriodRealization
