module

public import KsIndexLean.PlanarTestRadialIBP
public import Mathlib.Analysis.Normed.Operator.Mul

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

def weightedCircleTest (H : C(Circle₁, ℂ)) (ψ : ℂ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) : C(Circle₁, ℂ) :=
  r • (H * scaledCircleTest ψ hψ r)

def weightedCircleTestDeriv (H : C(Circle₁, ℂ)) (ψ : ℂ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) : C(Circle₁, ℂ) :=
  H * scaledCircleTest ψ hψ r + r • (H * scaledCircleRadialTest ψ hψ r)

lemma weightedCircleTest_hasDerivAt (H : C(Circle₁, ℂ))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    HasDerivAt (weightedCircleTest H ψ hψ) (weightedCircleTestDeriv H ψ hψ r) r := by
  convert (hasDerivAt_id r).smul ((scaledCircleTest_hasDerivAt hψ r).const_mul H) using 1 <;>
    first | rfl | simp [weightedCircleTestDeriv, add_comm]

lemma continuous_weightedCircleTestDeriv (H : C(Circle₁, ℂ))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (weightedCircleTestDeriv H ψ hψ) := by
  have hc : Continuous (scaledCircleTest ψ hψ) :=
    continuous_iff_continuousAt.mpr fun r => (scaledCircleTest_hasDerivAt hψ r).continuousAt
  exact (continuous_const.mul hc).add
    (continuous_id.smul (continuous_const.mul (continuous_scaledCircleRadialTest hψ)))

lemma weightedCircleFunctional_hasDerivAt (H : C(Circle₁, ℂ))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    HasDerivAt (fun t => circleTestFunctionalMap (weightedCircleTest H ψ hψ t))
      (circleTestFunctionalMap (weightedCircleTestDeriv H ψ hψ r)) r :=
  circleTestFunctionalMap.hasFDerivAt.comp_hasDerivAt r (weightedCircleTest_hasDerivAt H hψ r)

lemma contDiff_weightedCircleFunctional (H : C(Circle₁, ℂ))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ 1 (fun r => circleTestFunctionalMap (weightedCircleTest H ψ hψ r)) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r => (weightedCircleFunctional_hasDerivAt H hψ r).differentiableAt, ?_⟩
  have he : deriv (fun r => circleTestFunctionalMap (weightedCircleTest H ψ hψ r)) =
      fun r => circleTestFunctionalMap (weightedCircleTestDeriv H ψ hψ r) :=
    funext fun r => (weightedCircleFunctional_hasDerivAt H hψ r).deriv
  rw [he]
  exact circleTestFunctionalMap.continuous.comp (continuous_weightedCircleTestDeriv H hψ)

/-- The polar radius weight and any fixed circle multiplier are included in radial IBP. -/
theorem weighted_circle_radial_ibp_zero {a b : ℝ} (hab : a < b)
    {f g : ℝ → Lp ℂ 2 circleMeasure}
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b) f g 1)
    (hg : IntervalIntegrable g volume a b) (H : C(Circle₁, ℂ))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (ha : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ r in a..b,
      circleTestFunctionalMap (weightedCircleTest H ψ hψ r) (g r) +
      circleTestFunctionalMap (weightedCircleTestDeriv H ψ hψ r) (f r)) = 0 := by
  apply weak_radial_variable_ibp_zero hab hw hg
    (contDiff_weightedCircleFunctional H hψ).contDiffOn.absolutelyContinuousOnInterval
    (circleTestFunctionalMap.continuous.comp
      (continuous_weightedCircleTestDeriv H hψ)).continuousOn
    (Filter.Eventually.of_forall fun r _ => weightedCircleFunctional_hasDerivAt H hψ r)
  · simp [weightedCircleTest, scaledCircleTest_eq_zero hψ a ha]
  · simp [weightedCircleTest, scaledCircleTest_eq_zero hψ b hb]

end KsIndex.Trace
