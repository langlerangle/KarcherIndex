module

public import KsIndexLean.KarcherGeometricJacobiLinear

@[expose] public section


/-! The actual geometric Jacobi operator as a function on the period quotient. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The chart-local geometric operator descends to the quotient. -/
def geometricJacobi
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ :=
  Quotient.lift (R.geometricJacobiAt u) (fun q r hqr =>
    R.geometricJacobiAt_eq_of_quotient_eq u q r (Quotient.sound hqr))

@[simp] lemma geometricJacobi_apply_lift
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.geometricJacobi u (HeightLift.periodQuotientMap m q) = R.geometricJacobiAt u q := rfl

lemma isGeometricJacobi_iff
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.IsGeometricJacobi u ↔ R.geometricJacobi u = 0 := by
  constructor
  · intro hu
    funext x
    refine Quotient.inductionOn x ?_
    exact fun q => hu q
  · intro hu q
    exact congrFun hu (HeightLift.periodQuotientMap m q)

end KsIndex.KarcherData.PaperHalfPeriodRealization
