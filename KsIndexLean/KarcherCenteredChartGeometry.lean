module

public import KsIndexLean.KarcherLiftGeometry

@[expose] public section


/-! Differential, normal, and induced metric of the actual centered finite charts. -/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Coordinate expression of the normalized immersion in its already constructed atlas. -/
def centeredChart (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : ℂ → AmbientTriple :=
  centeredLiftAmbient R.C R.t ∘ (HeightLift.liftChart R.hC q).symm

lemma centeredChart_eq_translate (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.centeredChart q = fun z => ((R.t, 0, Real.pi) : AmbientTriple) +
      (HeightLift.ambient ∘ (HeightLift.liftChart R.hC q).symm) z := by
  funext z
  apply Prod.ext (by rfl)
  apply Prod.ext
  · simp [centeredChart, centeredLiftAmbient, HeightLift.ambient]
  · exact add_comm _ _

lemma centeredChart_finite_differential (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    HasFDerivAt (R.centeredChart q) (ewRealDifferential k w.val) w.val := by
  rw [centeredChart_eq_translate]
  exact (lifted_finite_differential (reflectionBasepoint k) w R.C R.hC q hq).const_add _

/-- The global unit field is the derivative-defined oriented normal of the
 actual centered immersion, in every finite lifted chart. -/
lemma normal_eq_centeredChart_finite (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) :
    R.normal q = chartUnitNormal (R.centeredChart q) w.val := by
  rw [R.normal_finite q w hq,
    ew_chartUnitNormal_eq_stereoNormal h.out w.property (R.centeredChart_finite_differential q w hq)]
  rfl

/-- Induced metric on all real tangent vectors in an actual finite lifted chart. -/
lemma centeredChart_finite_metric (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (d : ℂ) :
    euclideanSq (fderiv ℝ (R.centeredChart q) w.val d) = Surface.rho k w.val ^ 2 * ‖d‖ ^ 2 := by
  rw [(R.centeredChart_finite_differential q w hq).fderiv, ewRealDifferential_metric h.out]

end KsIndex.KarcherData.PaperHalfPeriodRealization
