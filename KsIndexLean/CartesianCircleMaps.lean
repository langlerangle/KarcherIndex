module

public import KsIndexLean.CartesianTestCancellation

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

def coordinateCircle (L : ℂ →L[ℝ] ℝ) : C(Circle₁, ℂ) := realAngularMap L L.continuous

def coordinateAngularTest (L : ℂ →L[ℝ] ℝ) (ψ : ℂ → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) : C(Circle₁, ℂ) :=
  realAngularMap (angularTestDeriv (fun z => scaledAngularTest ψ r z * L z))
    (contDiff_angularTestDeriv ((contDiff_scaledAngularTest hψ r).mul L.contDiff)).continuous

def cartesianCircleTest (ψ : ℂ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ)
    (v : ℂ) : C(Circle₁, ℂ) :=
  realAngularMap (fun z => fderiv ℝ ψ (r • z) v)
    ((((contDiff_infty_iff_fderiv.mp hψ).2.continuous).comp
      (continuous_id.const_smul r)).clm_apply continuous_const)

lemma weightedCircleTestDeriv_re {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    weightedCircleTestDeriv (coordinateCircle Complex.reCLM) ψ hψ r =
      r • cartesianCircleTest ψ hψ r 1 + coordinateAngularTest Complex.imCLM ψ hψ r := by
  apply ContinuousMap.ext
  intro w
  change (w : ℂ).re * (ψ (r • (w : ℂ)) : ℂ) +
      r • ((w : ℂ).re * (fderiv ℝ ψ (r • (w : ℂ)) w : ℂ)) =
    r • (fderiv ℝ ψ (r • (w : ℂ)) 1 : ℂ) +
      (angularTestDeriv (fun z => scaledAngularTest ψ r z * z.im) w : ℂ)
  simp only [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  congr 1
  have hc := cartesian_test_cancellation_one hψ r w
  simp only [Complex.real_smul] at hc
  nlinarith [hc]

lemma weightedCircleTestDeriv_im {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    weightedCircleTestDeriv (coordinateCircle Complex.imCLM) ψ hψ r =
      r • cartesianCircleTest ψ hψ r Complex.I - coordinateAngularTest Complex.reCLM ψ hψ r := by
  apply ContinuousMap.ext
  intro w
  change (w : ℂ).im * (ψ (r • (w : ℂ)) : ℂ) +
      r • ((w : ℂ).im * (fderiv ℝ ψ (r • (w : ℂ)) w : ℂ)) =
    r • (fderiv ℝ ψ (r • (w : ℂ)) Complex.I : ℂ) -
      (angularTestDeriv (fun z => scaledAngularTest ψ r z * z.re) w : ℂ)
  simp only [Complex.real_smul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub]
  congr 1
  have hc := cartesian_test_cancellation_I hψ r w
  simp only [Complex.real_smul] at hc
  nlinarith [hc]

/-- Angular graph membership rewrites the derivative-test pairing with its value-test pairing. -/
lemma coordinateAngularTest_pairing {F G : Lp ℂ 2 circleMeasure}
    (h : (F, G) ∈ circleAngularGraph) (L : ℂ →L[ℝ] ℝ)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (r : ℝ) :
    circleTestFunctionalMap (coordinateAngularTest L ψ hψ r) F =
      -circleTestFunctionalMap (coordinateCircle L * scaledCircleTest ψ hψ r) G := by
  have hh := circleAngularGraph_weighted_test h hψ L.contDiff r
  have he : realAngularMap (fun z => scaledAngularTest ψ r z * L z)
      ((contDiff_scaledAngularTest hψ r).mul L.contDiff).continuous =
      coordinateCircle L * scaledCircleTest ψ hψ r := by
    apply ContinuousMap.ext
    intro w
    change ((scaledAngularTest ψ r w * L w : ℝ) : ℂ) =
      (L w : ℂ) * (scaledAngularTest ψ r w : ℂ)
    rw [Complex.ofReal_mul, mul_comm]
  change circleTestFunctionalMap (coordinateAngularTest L ψ hψ r) F =
    -circleTestFunctionalMap (realAngularMap (fun z => scaledAngularTest ψ r z * L z)
      ((contDiff_scaledAngularTest hψ r).mul L.contDiff).continuous) G at hh
  rw [he] at hh
  exact hh

end KsIndex.Trace
