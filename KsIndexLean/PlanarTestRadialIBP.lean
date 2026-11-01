module

public import KsIndexLean.ScaledCircleTestCurve
public import KsIndexLean.RadialVariableIBP
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma circleTestFunctionalMap_apply (H : C(Circle₁, ℂ)) (f : Lp ℂ 2 circleMeasure) :
    circleTestFunctionalMap H f = inner ℂ (ContinuousMap.toLp 2 circleMeasure ℂ H) f := rfl

lemma contDiff_scaledCircleFunctional {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ 1 (fun r => circleTestFunctionalMap (scaledCircleTest ψ hψ r)) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r => (scaledCircleFunctional_hasDerivAt hψ r).differentiableAt, ?_⟩
  have he : deriv (fun r => circleTestFunctionalMap (scaledCircleTest ψ hψ r)) =
      fun r => circleTestFunctionalMap (scaledCircleRadialTest ψ hψ r) :=
    funext fun r => (scaledCircleFunctional_hasDerivAt hψ r).deriv
  rw [he]
  exact circleTestFunctionalMap.continuous.comp (continuous_scaledCircleRadialTest hψ)

/-- Radial integration by parts for an actual planar test restricted to each circle. -/
theorem planar_test_radial_ibp {a b : ℝ} (hab : a < b)
    {f g : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∫ r in a..b,
      inner ℂ (angularTestLp (scaledAngularTest ψ r)
        (contDiff_scaledAngularTest hψ r).continuous) (g r) +
      inner ℂ (angularTestLp (scaledRadialTest ψ r) (continuous_scaledRadialTest hψ r)) (f r)) =
      circleTestFunctionalMap (scaledCircleTest ψ hψ b) (representative hab f g b) -
      circleTestFunctionalMap (scaledCircleTest ψ hψ a) (representative hab f g a) := by
  exact weak_radial_variable_ibp hab hw hg
    (contDiff_scaledCircleFunctional hψ).contDiffOn.absolutelyContinuousOnInterval
    (circleTestFunctionalMap.continuous.comp (continuous_scaledCircleRadialTest hψ)).continuousOn
    (Filter.Eventually.of_forall fun r _ => scaledCircleFunctional_hasDerivAt hψ r)

lemma scaledCircleTest_eq_zero {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ)
    (hz : ∀ w : Circle₁, ψ (r • (w : ℂ)) = 0) : scaledCircleTest ψ hψ r = 0 := by
  ext w
  change (ψ (r • (w : ℂ)) : ℂ) = 0
  rw [hz w, Complex.ofReal_zero]

/-- Tests vanishing on the endpoint circles have no radial boundary contribution. -/
theorem planar_test_radial_ibp_zero {a b : ℝ} (hab : a < b)
    {f g : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (ha : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ r in a..b,
      inner ℂ (angularTestLp (scaledAngularTest ψ r)
        (contDiff_scaledAngularTest hψ r).continuous) (g r) +
      inner ℂ (angularTestLp (scaledRadialTest ψ r) (continuous_scaledRadialTest hψ r)) (f r)) =
      0 := by
  rw [planar_test_radial_ibp hab hw hg hψ,
    scaledCircleTest_eq_zero hψ a ha, scaledCircleTest_eq_zero hψ b hb]
  simp

end KsIndex.Trace
