module

public import KsIndexLean.SphericalGlobalOperator
public import KsIndexLean.KarcherCopyJacobi
public import KsIndexLean.KarcherPeriodProjectionSmooth

@[expose] public section


/-! The spherical Schrödinger operator intertwines with the conformally
rescaled geometric Jacobi operator on the actual EW period quotient. -/
noncomputable section
open Set Topology Filter
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open Spherical

/-- Conformal rescaling relates the geometric disk operator to the round
spherical coordinate operator, with the full multiplier retained. -/
lemma diskJacobi_spherical_rescale {k : ℕ} (hk : 2 ≤ k) {z : ℂ}
    (hz : z ∉ Surface.punctures k) (f : ℂ → ℂ) :
    ((Surface.rho k z ^ 2 / stereoAreaDensity z : ℝ) : ℂ) * diskJacobi k f z =
      sphericalChartJacobiOperator k f z := by
  rw [diskJacobi_eq_flat hk hz, sphericalChartJacobiOperator_eq]
  have hr : (Surface.rho k z : ℂ)^2 ≠ 0 := by
    exact_mod_cast (ne_of_gt (rho_sq_pos hk hz))
  have hr' : (Surface.rho k z : ℂ) ≠ 0 := by
    intro he; apply hr; rw [he]; norm_num
  push_cast
  field_simp [hr']

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The actual quotient projection viewed as a map to the round sphere. -/
def sphericalProjection
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    Sphere := (HeightLift.quotientProjection m x).val

/-- The actual spherical projection is smooth for the quotient's registered atlas. -/
lemma sphericalProjection_contMDiff :
    let := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (R.sphericalProjection (m := m)) := by
  let := HeightLift.periodChartedSpace R.hC m
  exact (contMDiff_subtype_val (U := ParameterAtlas.parameterOpen h.out)).comp
    (HeightLift.quotientProjection_contMDiff R.hC m)

/-- Smooth spherical functions pull back to smooth functions on the actual quotient. -/
lemma sphericalPullback_contMDiff {f : Sphere → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) :
    let := HeightLift.periodChartedSpace R.hC m
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (f ∘ R.sphericalProjection (m := m)) := by
  let := HeightLift.periodChartedSpace R.hC m
  exact hf.comp R.sphericalProjection_contMDiff

/-- Quotient coordinates project to the parameter chart on a neighborhood
of the chart center. -/
lemma sphericalProjection_chart_germ
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    (R.sphericalProjection ∘
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm) =ᶠ[
        𝓝 (R.chartCenter q)]
      (fun z => ((chartAt ℂ (HeightLift.projection q)).symm z).val) := by
  let e := HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)
  have hc : e (HeightLift.periodQuotientMap m q) = R.chartCenter q := by
    rw [HeightLift.periodChart_apply, chartCenter, HeightLift.liftChart_apply]
    rfl
  have ht := e.open_target.mem_nhds (e.map_source (HeightLift.periodChart_mem R.hC m _))
  rw [hc] at ht
  filter_upwards [ht] with z hz
  exact congrArg Subtype.val (HeightLift.periodChart_symm_projection R.hC m hz)

/-- Finite-coordinate pullback germ for any spherical scalar function. -/
lemma sphericalPullback_finite_germ (f : Sphere → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    ((f ∘ R.sphericalProjection) ∘
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm) =ᶠ[𝓝 w.val]
      (f ∘ sphereChart) := by
  have hg := R.sphericalProjection_chart_germ (m := m) q
  rw [R.chartCenter_finite q w hq, hq] at hg
  filter_upwards [hg, ParameterAtlas.finite_chart_inverse_germ w] with z hz hzw
  exact congrArg f (hz.trans hzw)

/-- Infinity-coordinate pullback germ, including the regular pole. -/
lemma sphericalPullback_infinity_germ (f : Sphere → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) :
    ((f ∘ R.sphericalProjection) ∘
      (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm) =ᶠ[𝓝 (0 : ℂ)]
      (f ∘ infinitySphereChart) := by
  have hg := R.sphericalProjection_chart_germ (m := m) q
  rw [R.chartCenter_infinity q hq, hq] at hg
  filter_upwards [hg, ParameterAtlas.infinity_chart_inverse_germ (k := k)] with z hz hzw
  exact congrArg f (hz.trans hzw)

/-- The precise spherical intertwining identity at every lift of an actual
EW period-quotient point. Both finite and infinity centers are included. -/
theorem geometricJacobiAt_spherical_pullback
    {f : Sphere → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    ((Surface.rho k (R.chartCenter q) ^ 2 / stereoAreaDensity (R.chartCenter q) : ℝ) : ℂ) *
      R.geometricJacobiAt (f ∘ R.sphericalProjection (m := m)) q =
      sphereJacobiOperator k f (HeightLift.projection q).val := by
  rw [R.geometricJacobiAt_eq_diskJacobi]
  rcases parameterSphere_cases (HeightLift.projection q) with hq | ⟨w, hw⟩
  · rw [R.chartCenter_infinity q hq,
      diskJacobi_congr (R.sphericalPullback_infinity_germ (m := m) f q hq),
      diskJacobi_spherical_rescale h.out (zero_not_puncture h.out), hq]
    exact (sphereJacobiOperator_infinity_smooth h.out hf 0).symm
  · rw [R.chartCenter_finite q w hw.symm,
      diskJacobi_congr (R.sphericalPullback_finite_germ (m := m) f q w hw.symm),
      diskJacobi_spherical_rescale h.out w.property, ← hw]
    exact (sphereJacobiOperator_finite k f w.val).symm

/-- The positive conformal multiplier on the quotient. The selected coordinate
is finite away from the north pole and the regular infinity coordinate there. -/
def sphericalJacobiMultiplier
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : ℝ :=
  let z := chartAt ℂ (HeightLift.quotientProjection m x) (HeightLift.quotientProjection m x)
  Surface.rho k z ^ 2 / stereoAreaDensity z

lemma sphericalJacobiMultiplier_lift
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.sphericalJacobiMultiplier (HeightLift.periodQuotientMap m q) =
      Surface.rho k (R.chartCenter q) ^ 2 / stereoAreaDensity (R.chartCenter q) := by
  simp only [sphericalJacobiMultiplier, chartCenter, HeightLift.liftChart_apply]
  rfl

/-- In finite coordinates this is exactly the multiplier displayed in the paper. -/
lemma sphericalJacobiMultiplier_finite
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (w : PuncturedPlane k) (hx : HeightLift.quotientProjection m x = finiteParameter w) :
    R.sphericalJacobiMultiplier x = Surface.rho k w.val ^ 2 * (1 + ‖w.val‖ ^ 2)^2 / 4 := by
  simp only [sphericalJacobiMultiplier, hx, ParameterAtlas.parameter_chartAt_finite,
    stereoAreaDensity_eq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- At infinity the regular coordinate gives a finite, nonsingular multiplier. -/
lemma sphericalJacobiMultiplier_infinity
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m)
    (hx : HeightLift.quotientProjection m x = infinityParameter k) :
    R.sphericalJacobiMultiplier x = Surface.rho k 0 ^ 2 / 4 := by
  simp [sphericalJacobiMultiplier, hx, ParameterAtlas.parameter_chartAt_infinity,
    stereoAreaDensity_eq]

/-- The multiplier remains strictly positive at the regular infinity point. -/
lemma sphericalJacobiMultiplier_pos
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    0 < R.sphericalJacobiMultiplier x := by
  unfold sphericalJacobiMultiplier
  rcases parameterSphere_cases (HeightLift.quotientProjection m x) with hx | ⟨w, hw⟩
  · rw [hx, ParameterAtlas.parameter_chartAt_infinity]
    exact div_pos (rho_sq_pos h.out (zero_not_puncture h.out)) (stereoAreaDensity_pos 0)
  · rw [← hw, ParameterAtlas.parameter_chartAt_finite]
    exact div_pos (rho_sq_pos h.out w.property) (stereoAreaDensity_pos w.val)

/-- The paper's conformally rescaled operator on the actual EW period quotient. -/
def sphericalGeometricJacobi
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (x : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : ℂ :=
  (R.sphericalJacobiMultiplier x : ℂ) * R.geometricJacobi u x

/-- Full operator intertwining, as an equality of functions on the quotient. -/
theorem sphericalGeometricJacobi_pullback
    {f : Sphere → ℂ} (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) :
    R.sphericalGeometricJacobi (f ∘ R.sphericalProjection (m := m)) =
      (sphereJacobiOperator k f) ∘ R.sphericalProjection := by
  funext x
  refine Quotient.inductionOn x ?_
  intro q
  change (R.sphericalJacobiMultiplier (HeightLift.periodQuotientMap m q) : ℂ) *
    R.geometricJacobiAt (f ∘ R.sphericalProjection) q = _
  rw [R.sphericalJacobiMultiplier_lift]
  exact R.geometricJacobiAt_spherical_pullback (m := m) hf q

end PaperHalfPeriodRealization
end KsIndex.KarcherData
