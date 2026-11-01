module

public import KsIndexLean.KarcherInfinityLiftGeometry

@[expose] public section


/-! Global first-order geometry of the same normalized intrinsic immersion. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The center coordinate in the already registered lifted atlas. -/
def chartCenter (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : ℂ :=
  HeightLift.liftChart R.hC q q

lemma chartCenter_finite (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) : R.chartCenter q = w.val := by
  rw [chartCenter, HeightLift.liftChart_apply, hq, ParameterAtlas.parameter_chartAt_finite]

lemma chartCenter_infinity (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) : R.chartCenter q = 0 := by
  rw [chartCenter, HeightLift.liftChart_apply, hq, ParameterAtlas.parameter_chartAt_infinity]

/-- The continuous unit field is the actual positively oriented normal of the
 normalized immersion at EVERY point, including every lift of infinity. -/
theorem normal_eq_centeredChart (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.normal q = chartUnitNormal (R.centeredChart q) (R.chartCenter q) := by
  rcases parameterSphere_cases (HeightLift.projection q) with hq | ⟨w, hw⟩
  · rw [R.chartCenter_infinity q hq]
    exact R.normal_eq_centeredChart_infinity q hq
  · rw [R.chartCenter_finite q w hw.symm]
    exact R.normal_eq_centeredChart_finite q w hw.symm

/-- The positive induced conformal factor in the atlas, with its infinity
 value in the infinity coordinate rather than a totalized finite expression. -/
theorem centeredChart_metric (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    0 < Surface.rho k (R.chartCenter q) ^ 2 ∧
      ∀ d : ℂ, euclideanSq (fderiv ℝ (R.centeredChart q) (R.chartCenter q) d) =
        Surface.rho k (R.chartCenter q) ^ 2 * ‖d‖ ^ 2 := by
  rcases parameterSphere_cases (HeightLift.projection q) with hq | ⟨w, hw⟩
  · rw [R.chartCenter_infinity q hq]
    exact ⟨rho_sq_pos h.out (not_puncture_of_norm_lt_one h.out (by simp)),
      R.centeredChart_infinity_metric q hq⟩
  · rw [R.chartCenter_finite q w hw.symm]
    exact ⟨rho_sq_pos h.out w.property, R.centeredChart_finite_metric q w hw.symm⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
