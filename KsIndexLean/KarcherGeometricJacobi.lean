module

public import KsIndexLean.KarcherAreaLiftAgreement
public import KsIndexLean.KarcherChartMetricField
public import KsIndexLean.KarcherGlobalCurvature

@[expose] public section


/-! The Jacobi equation on the actual EW period quotient, expressed through
its immersion charts. Boundedness is a uniform pointwise bound on the quotient;
neither compact support nor geometric square integrability is required. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The area density of the actual immersion at any registered chart center. -/
lemma centeredChart_areaDensity_center
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    chartAreaDensity (R.centeredChart q) (R.chartCenter q) =
      Surface.rho k (R.chartCenter q) ^ 2 := by
  rcases parameterSphere_cases (HeightLift.projection q) with hq | ⟨w, hw⟩
  · rw [R.chartCenter_infinity q hq]
    exact R.centeredChart_areaDensity_infinity q hq
  · rw [R.chartCenter_finite q w hw.symm]
    exact R.centeredChart_areaDensity q w hw.symm

/-- The actual chart Laplace–Beltrami operator, at finite and infinity centers. -/
lemma centeredChart_laplaceBeltrami
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (f : ℂ → ℂ) :
    conformalLaplaceBeltrami (fun z => chartAreaDensity (R.centeredChart q) z)
      f (R.chartCenter q) = Surface.laplacianG k f (R.chartCenter q) := by
  rcases parameterSphere_cases (HeightLift.projection q) with hq | ⟨w, hw⟩
  · rw [R.chartCenter_infinity q hq]
    exact R.centeredChart_infinity_laplaceBeltrami q hq f
  · rw [R.chartCenter_finite q w hw.symm]
    exact R.centeredChart_finite_laplaceBeltrami q w hw.symm f

/-- The geometric Jacobi operator in the chart centered at a lift of the quotient
point. Its coefficients are computed from the actual immersion. -/
def geometricJacobiAt
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : ℂ :=
  let f := u ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm
  conformalLaplaceBeltrami (fun z => chartAreaDensity (R.centeredChart q) z)
    f (R.chartCenter q) +
    (conformalSecondFundamentalNorm (R.centeredChart q) (R.chartCenter q)
      (chartAreaDensity (R.centeredChart q) (R.chartCenter q)) : ℂ) ^ 2 *
      u (HeightLift.periodQuotientMap m q)

/-- The equation is imposed at every lift, so no selected representative is
part of the definition. Independence of lifts is established separately. -/
def IsGeometricJacobi
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) : Prop :=
  ∀ q, R.geometricJacobiAt u q = 0

/-- Bounded smooth solutions of the actual geometric equation. -/
def IsBoundedGeometricJacobi
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) : Prop :=
  letI := HeightLift.periodChartedSpace R.hC m
  ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u ∧
    (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ R.IsGeometricJacobi u

/-- Coordinate expression obtained from the actual metric and curvature. -/
lemma geometricJacobiAt_eq
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.geometricJacobiAt u q =
      Surface.laplacianG k
        (u ∘ (HeightLift.periodChart R.hC m (HeightLift.periodQuotientMap m q)).symm)
        (R.chartCenter q) +
      (Surface.absA k (R.chartCenter q) : ℂ) ^ 2 * u (HeightLift.periodQuotientMap m q) := by
  dsimp only [geometricJacobiAt]
  rw [R.centeredChart_laplaceBeltrami, R.centeredChart_areaDensity_center,
    (R.centeredChart_curvature q).2]

/-- Changing the lift of a quotient point does not change the geometric operator. -/
lemma geometricJacobiAt_eq_of_quotient_eq
    (u : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q r : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hqr : HeightLift.periodQuotientMap m q = HeightLift.periodQuotientMap m r) :
    R.geometricJacobiAt u q = R.geometricJacobiAt u r := by
  have hp : HeightLift.projection q = HeightLift.projection r :=
    congrArg (HeightLift.quotientProjection m) hqr
  have hc : R.chartCenter q = R.chartCenter r := by
    simp only [chartCenter, HeightLift.liftChart_apply, hp]
  rw [R.geometricJacobiAt_eq, R.geometricJacobiAt_eq, hqr, hc]

end KsIndex.KarcherData.PaperHalfPeriodRealization
