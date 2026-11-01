module

public import KsIndexLean.KarcherRealSymmetries

@[expose] public section


/-! Real, height-preserving conjugation on the same normalized EW carrier. -/
noncomputable section
namespace KsIndex.KarcherData
open scoped ParameterAtlas PeriodicAmbient
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The reflection in y=0 keeps the actual real height, not just its period class. -/
def conjugationLift (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    PeriodicEWCarrier h.out (reflectionBasepoint k) R.C :=
  ⟨(parameterConjugation (HeightLift.projection q), HeightLift.height q), by
    have he := congrArg (fun p : PeriodTarget => p.2.2) (R.symmetries.1 (HeightLift.projection q))
    change (Real.pi : AddCircle (2 * Real.pi)) +
        (extendedEWMap h.out (reflectionBasepoint k) R.C
          (parameterConjugation (HeightLift.projection q))).2.2 =
      (Real.pi : AddCircle (2 * Real.pi)) +
        (extendedEWMap h.out (reflectionBasepoint k) R.C (HeightLift.projection q)).2.2 at he
    exact q.property.trans (add_left_cancel he).symm⟩

lemma conjugationLift_projection (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.projection (R.conjugationLift q) = parameterConjugation (HeightLift.projection q) := rfl

lemma conjugationLift_height (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    HeightLift.height (R.conjugationLift q) = HeightLift.height q := rfl

lemma continuous_conjugationLift (R : PaperHalfPeriodRealization k) :
    Continuous R.conjugationLift := by
  apply Continuous.subtype_mk
  exact ((continuous_parameterConjugation k).comp HeightLift.continuous_projection).prodMk
    HeightLift.continuous_height

lemma conjugationLift_involutive (R : PaperHalfPeriodRealization k) :
    Function.Involutive R.conjugationLift := by
  intro q
  apply Subtype.ext
  exact Prod.ext (parameterConjugation_involutive k (HeightLift.projection q)) rfl

lemma conjugationLift_ambient (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    centeredLiftAmbient R.C R.t (R.conjugationLift q) =
      ((centeredLiftAmbient R.C R.t q).1, -(centeredLiftAmbient R.C R.t q).2.1,
        (centeredLiftAmbient R.C R.t q).2.2) := by
  have hp : projectPeriod (centeredLiftAmbient R.C R.t (R.conjugationLift q)) =
      PeriodTarget.reflY (projectPeriod (centeredLiftAmbient R.C R.t q)) := by
    rw [project_centeredLiftAmbient, project_centeredLiftAmbient, conjugationLift_projection]
    exact R.symmetries.1 (HeightLift.projection q)
  apply Prod.ext
  · have hx := congrArg (fun p : PeriodTarget => p.1) hp
    simpa only [projectPeriod, PeriodTarget.reflY] using hx
  · apply Prod.ext
    · have hy := congrArg (fun p : PeriodTarget => p.2.1) hp
      simpa only [projectPeriod, PeriodTarget.reflY] using hy
    · rfl

end PaperHalfPeriodRealization
end KsIndex.KarcherData
