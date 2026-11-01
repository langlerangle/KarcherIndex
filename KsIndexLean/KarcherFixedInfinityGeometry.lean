module

public import KsIndexLean.KarcherContinuousExtensionUnique

@[expose] public section


/-! The constructed infinity geometry belongs to any actual continuous EW extension. -/
noncomputable section
open scoped ContDiff
namespace KsIndex.KarcherData

/-- Transfer the constructed smooth infinity primitive to the very same extension
 used by the global realization; its additive constant is not a new assumption. -/
theorem exists_fixed_infinity_geometry {k : ℕ} [h : Fact (2 ≤ k)]
    (b : PuncturedPlane k) (C : PeriodTarget)
    (hC : Continuous (extendedEWMap h.out b C)) :
    ∃ r : ℝ, ∃ _hr0 : 0 < r, ∃ hr1 : r < 1,
    ∃ X : ℂ → AmbientTriple,
      X 0 = 0 ∧ ContDiffOn ℝ ∞ X (Metric.ball (0 : ℂ) r) ∧
      HarmonicCoordinates X (Metric.ball (0 : ℂ) r) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, HasFDerivAt X (infinityRealDifferential k v) v) ∧
      (∀ v : Metric.ball (0 : ℂ) r,
        extendedEWMap h.out b C (infinityParameterChart h.out hr1.le v) =
          C + projectPeriod (X v.val)) ∧
      (∀ v ∈ Metric.ball (0 : ℂ) r, euclideanSq (chartUnitNormal X v) = 1 ∧
        chartMeanCurvature X v = 0 ∧
        conformalSecondFundamentalNorm X v (Surface.rho k v ^ 2) = Surface.absA k v) := by
  obtain ⟨r, hr0, hr1, X, D, hz, hs, hh, hd, _, he, hg⟩ :=
    exists_curvature_infinity_chart h.out b
  have hD : Continuous (extendedEWMap h.out b D) :=
    continuous_extendedEWMap h.out b hr0 hr1.le hz hs.continuousOn he
  have hCD : C = D := continuous_infinity_value_unique b hC hD
  subst D
  exact ⟨r, hr0, hr1, X, hz, hs, hh, hd,
    extendedEWMap_infinityChart h.out b hr1.le hz he, hg⟩

end KsIndex.KarcherData
