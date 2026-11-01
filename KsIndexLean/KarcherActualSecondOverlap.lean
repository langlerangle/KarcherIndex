module

public import KsIndexLean.KarcherComplexAtlas
public import KsIndexLean.KarcherNormalRegularity

@[expose] public section


/-! Covariance of the Hessian-defined second fundamental form on the actual atlas. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma centeredChart_cross_sq_pos (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ (HeightLift.liftChart R.hC q).target) :
    0 < euclideanSq (euclideanCross (fderiv ℝ (R.centeredChart q) z 1)
      (fderiv ℝ (R.centeredChart q) z Complex.I)) := by
  have hu := R.normal_unit ((HeightLift.liftChart R.hC q).symm z)
  rw [← R.chartUnitNormal_eq_global q hz] at hu
  by_contra! hn
  have hn0 : euclideanSq (euclideanCross (fderiv ℝ (R.centeredChart q) z 1)
      (fderiv ℝ (R.centeredChart q) z Complex.I)) = 0 := by
    exact le_antisymm hn (by unfold euclideanSq; positivity)
  have hzero : chartUnitNormal (R.centeredChart q) z = 0 := by
    unfold chartUnitNormal
    rw [hn0]
    simp
  rw [hzero] at hu
  norm_num [euclideanSq] at hu

lemma centeredChart_normal_differentiableAt (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ (HeightLift.liftChart R.hC q).target) :
    DifferentiableAt ℝ (chartUnitNormal (R.centeredChart q)) z :=
  chartUnitNormal_differentiableAt ((R.centeredChart_contDiffAt q hz).of_le (by simp))
    (R.centeredChart_cross_sq_pos q hz)

lemma centeredChart_second_eq (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ (HeightLift.liftChart R.hC q).target) (a b : ℂ) :
    secondFundamentalForm (R.centeredChart q) z a b =
      -euclideanDot (fderiv ℝ (chartUnitNormal (R.centeredChart q)) z a)
        (fderiv ℝ (R.centeredChart q) z b) := by
  apply secondFundamentalForm_eq_neg_normal_derivative
    ((R.centeredChart_contDiffAt q hz).of_le (by simp))
    (R.centeredChart_normal_differentiableAt q hz) rfl a b
  filter_upwards [(HeightLift.liftChart R.hC q).open_target.mem_nhds hz] with w hw
  rw [coordinateTangent_eq ((R.centeredChart_contDiffAt q hw).differentiableAt (by simp))]
  exact chartUnitNormal_orthogonal _ _ _

/-- Full two-slot covariance of II, with orientation and normal regularity
proved for these actual charts rather than supplied as hypotheses. -/
theorem secondFundamentalForm_chart_overlap (R : PaperHalfPeriodRealization k)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) {z : ℂ}
    (hz : z ∈ ((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).source) (a b : ℂ) :
    let c := HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm
    secondFundamentalForm (R.centeredChart q) z a b =
      secondFundamentalForm (R.centeredChart r) (c z)
        (fderiv ℝ c z a) (fderiv ℝ c z b) := by
  dsimp only
  let c := HeightLift.liftChart R.hC r ∘ (HeightLift.liftChart R.hC q).symm
  have ht : c z ∈ (HeightLift.liftChart R.hC r).target :=
    (HeightLift.liftChart R.hC r).map_source hz.2
  have hd := (R.centeredChart_contDiffAt r ht).differentiableAt (by simp)
  have hc : DifferentiableAt ℝ c z :=
    (R.chartTransition_contDiffAt q r hz).differentiableAt (by simp)
  have hn := R.centeredChart_normal_differentiableAt r ht
  have he : R.centeredChart q =ᶠ[𝓝 z] R.centeredChart r ∘ c :=
    R.centeredChart_overlap_germ q r hz
  have hne : chartUnitNormal (R.centeredChart q) =ᶠ[𝓝 z]
      (chartUnitNormal (R.centeredChart r) ∘ c) := by
    filter_upwards [((HeightLift.liftChart R.hC q).symm.trans
      (HeightLift.liftChart R.hC r)).open_source.mem_nhds hz] with w hw
    exact R.chartUnitNormal_chart_overlap q r hw
  rw [R.centeredChart_second_eq q hz.1, R.centeredChart_second_eq r ht]
  simp only [hne.fderiv_eq, he.fderiv_eq, fderiv_comp z hn hc,
    fderiv_comp z hd hc, ContinuousLinearMap.comp_apply]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
