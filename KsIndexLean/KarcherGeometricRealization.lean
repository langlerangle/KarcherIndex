module

public import KsIndexLean.KarcherActualSecondOverlap
public import KsIndexLean.KarcherMetricTensor
public import KsIndexLean.KarcherHalfPeriodHomeomorph
public import KsIndexLean.KarcherCoverUniqueness

@[expose] public section


/-! Same-witness existence for the actual normalized EW geometry.
This theorem assembles geometric data already derived from the EW integrals.
It is not the complete ewcover proposition: the distinguished diameter clause
and disk-chain analytic transport are separate from this assembly.
-/
noncomputable section
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
  KsIndex.KarcherData.PeriodicAmbient
namespace KsIndex.KarcherData

/-- One EW extension, positional normalization and lifted atlas simultaneously
supply the conformal covering, smooth immersion, global oriented unit normal,
induced metric, minimality, curvature and closed-half-period homeomorphism.
All occurrences below use that same realization R. -/
theorem exists_normalized_geometric_realization {k : ℕ} [h : Fact (2 ≤ k)] :
    ∃ R : PaperHalfPeriodRealization k,
      (let := HeightLift.liftChartedSpace R.hC
       ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ∞
         (HeightLift.projection (F := extendedEWMap h.out (reflectionBasepoint k) R.C)) ∧
       ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple) ∞
         (centeredLiftAmbient (k := k) R.C R.t) ∧
       ∀ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
         IsDiffImmersionAt 𝓘(ℝ, ℂ) 𝓘(ℝ, AmbientTriple)
           (centeredLiftAmbient (k := k) R.C R.t) q) ∧
      IsCoveringMap (HeightLift.projection
        (F := extendedEWMap h.out (reflectionBasepoint k) R.C)) ∧
      Continuous R.normal ∧
      Continuous R.diskHomeomorph.symm ∧
      ∀ q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C,
        euclideanSq (R.normal q) = 1 ∧
        R.normal q = chartUnitNormal (R.centeredChart q) (R.chartCenter q) ∧
        0 < Surface.rho k (R.chartCenter q) ^ 2 ∧
        (∀ a b : ℂ, firstFundamentalForm (R.centeredChart q) (R.chartCenter q) a b =
          Surface.rho k (R.chartCenter q) ^ 2 * (a.re * b.re + a.im * b.im)) ∧
        chartMeanCurvature (R.centeredChart q) (R.chartCenter q) = 0 ∧
        conformalSecondFundamentalNorm (R.centeredChart q) (R.chartCenter q)
          (Surface.rho k (R.chartCenter q) ^ 2) = Surface.absA k (R.chartCenter q) := by
  obtain ⟨R⟩ := exists_paperHalfPeriodRealization (k := k)
  refine ⟨R, ⟨R.holomorphic_covering.1, R.centered_geometry⟩, R.covering,
    R.continuous_normal, R.diskHomeomorph.symm.continuous, ?_⟩
  intro q
  exact ⟨R.normal_unit q, R.normal_eq_centeredChart q, (R.centeredChart_metric q).1,
    R.centeredChart_metric_tensor q, R.centeredChart_curvature q⟩

end KsIndex.KarcherData
