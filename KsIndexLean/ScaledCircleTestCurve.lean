module

public import KsIndexLean.ContinuousMapCurve
public import KsIndexLean.AngularVariableTests
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

def scaledCircleTest (ψ : ℂ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    C(Circle₁, ℂ) := realAngularMap (scaledAngularTest ψ r)
      (contDiff_scaledAngularTest hψ r).continuous

def scaledRadialTest (ψ : ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ := fderiv ℝ ψ (r • z) z

lemma continuous_scaledRadialTest {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    Continuous (scaledRadialTest ψ r) := by
  change Continuous (fun z : ℂ => fderiv ℝ ψ (r • z) z)
  exact (((contDiff_infty_iff_fderiv.mp hψ).2.continuous).comp
    (continuous_id.const_smul r)).clm_apply continuous_id

def scaledCircleRadialTest (ψ : ℂ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    C(Circle₁, ℂ) := realAngularMap (scaledRadialTest ψ r) (continuous_scaledRadialTest hψ r)

lemma continuous_scaledCircleRadialTest {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous (scaledCircleRadialTest ψ hψ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact Complex.continuous_ofReal.comp
    ((((contDiff_infty_iff_fderiv.mp hψ).2.continuous).comp
      (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))).clm_apply
      (continuous_subtype_val.comp continuous_snd))

/-- Smooth planar tests restricted to circles differentiate in the sup norm. -/
theorem scaledCircleTest_hasDerivAt {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    HasDerivAt (scaledCircleTest ψ hψ) (scaledCircleRadialTest ψ hψ r) r := by
  apply continuousMap_hasDerivAt_of_pointwise (continuous_scaledCircleRadialTest hψ)
  intro t w
  have hs : HasDerivAt (fun s : ℝ => s • (w : ℂ)) (w : ℂ) t := by
    simpa using (hasDerivAt_id t).smul_const (w : ℂ)
  exact ((hψ.differentiable (by simp) (t • (w : ℂ))).hasFDerivAt.comp_hasDerivAt t hs).ofReal_comp

/-- Bounded real-linear map from continuous tests to their complex L² pairing functionals. -/
def circleTestFunctionalMap : C(Circle₁, ℂ) →L[ℝ] (Lp ℂ 2 circleMeasure →L[ℝ] ℂ) :=
  (isBoundedBilinearMap_inner (𝕜 := ℂ) (E := Lp ℂ 2 circleMeasure)).toContinuousLinearMap.comp
    (ContinuousMap.toLp 2 circleMeasure ℝ)

/-- The radius derivative passes through the bounded L² pairing operator. -/
theorem scaledCircleFunctional_hasDerivAt {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    HasDerivAt (fun t => circleTestFunctionalMap (scaledCircleTest ψ hψ t))
      (circleTestFunctionalMap (scaledCircleRadialTest ψ hψ r)) r :=
  circleTestFunctionalMap.hasFDerivAt.comp_hasDerivAt r (scaledCircleTest_hasDerivAt hψ r)

end KsIndex.Trace
