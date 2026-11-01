module

public import KsIndexLean.KarcherPeriodicSmooth
public import KsIndexLean.KarcherGeometricJacobi
public import KsIndexLean.JacobiFamily

@[expose] public section


/-! The Jacobi equation on the periodic lift and on its period quotient. -/
noncomputable section
open Set Topology
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- Jacobi operator of the actual lifted immersion, evaluated in its own chart. -/
def liftJacobiAt
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : ℂ :=
  conformalLaplaceBeltrami (fun z => chartAreaDensity (R.centeredChart q) z)
    (f ∘ (HeightLift.liftChart R.hC q).symm) (R.chartCenter q) +
    (conformalSecondFundamentalNorm (R.centeredChart q) (R.chartCenter q)
      (chartAreaDensity (R.centeredChart q) (R.chartCenter q)) : ℂ) ^ 2 * f q

lemma liftJacobiAt_pullback
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.liftJacobiAt (HeightLift.periodicFunctionEquiv m g).val q = R.geometricJacobiAt g q := by
  dsimp only [liftJacobiAt, geometricJacobiAt]
  rw [R.centeredChart_laplaceBeltrami, R.centeredChart_laplaceBeltrami]
  simp only [Surface.laplacianG]
  have he := R.centeredChart_scalar_pullback_germ g q
  have hl := JacobiFamily.laplacian_congr he
  change _ * Surface.laplacian
    (g ∘ HeightLift.periodQuotientMap m ∘ (HeightLift.liftChart R.hC q).symm) _ + _ = _
  rw [hl]
  rfl

/-- Bounded smooth Jacobi fields on the infinite lift that are periodic by m periods. -/
def IsBoundedPeriodicJacobi
    (f : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C → ℂ) : Prop :=
  letI := HeightLift.liftChartedSpace R.hC
  f ∈ HeightLift.periodicFunctions m ∧
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f ∧
    (∃ C : ℝ, ∀ q, ‖f q‖ ≤ C) ∧ ∀ q, R.liftJacobiAt f q = 0

lemma boundedPeriodicJacobi_pullback_iff
    (g : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    R.IsBoundedPeriodicJacobi (m := m) (HeightLift.periodicFunctionEquiv m g).val ↔
      R.IsBoundedGeometricJacobi g := by
  let := HeightLift.liftChartedSpace R.hC
  let := HeightLift.periodChartedSpace R.hC m
  change (_ ∧ _ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
  have hper := (HeightLift.periodicFunctionEquiv
    (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m g).property
  have hb : (∃ C : ℝ, ∀ q, ‖(HeightLift.periodicFunctionEquiv m g).val q‖ ≤ C) ↔
      (∃ C : ℝ, ∀ x, ‖g x‖ ≤ C) := by
    exact exists_congr (fun C => HeightLift.periodicFunctionEquiv_norm_bound_iff m g C)
  have hj : (∀ q, R.liftJacobiAt (HeightLift.periodicFunctionEquiv m g).val q = 0) ↔
      R.IsGeometricJacobi g := by
    simp only [liftJacobiAt_pullback, IsGeometricJacobi]
  rw [and_iff_right hper, HeightLift.periodicFunctionEquiv_contMDiff_iff R.hC m g, hb, hj]

end KsIndex.KarcherData.PaperHalfPeriodRealization
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.liftJacobiAt_pullback
#print axioms KsIndex.KarcherData.PaperHalfPeriodRealization.boundedPeriodicJacobi_pullback_iff
