module

public import KsIndexLean.AngularCoordinateTests
public import KsIndexLean.WeightedCircleTest

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

/-- The real-coordinate angular term cancels the extra term from the polar radius weight. -/
lemma cartesian_test_cancellation_one {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (r : ℝ) (w : Circle₁) :
    ψ (r • (w : ℂ)) * (w : ℂ).re +
        r * (w : ℂ).re * fderiv ℝ ψ (r • (w : ℂ)) w =
      r * fderiv ℝ ψ (r • (w : ℂ)) 1 +
        angularTestDeriv (fun z => scaledAngularTest ψ r z * z.im) w := by
  rw [angularTestDeriv_scaled_mul (H := Complex.im) hψ
      Complex.imCLM.contDiff,
    angularTestDeriv_im, map_smul,
    circle_frame_apply_one (fderiv ℝ ψ (r • (w : ℂ))) w]
  change _ = r * ((w : ℂ).re * _ - (w : ℂ).im * _) +
    (ψ (r • (w : ℂ)) * (w : ℂ).re + (w : ℂ).im * (r * _))
  ring

/-- The imaginary-coordinate formula has the opposite angular sign. -/
lemma cartesian_test_cancellation_I {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (r : ℝ) (w : Circle₁) :
    ψ (r • (w : ℂ)) * (w : ℂ).im +
        r * (w : ℂ).im * fderiv ℝ ψ (r • (w : ℂ)) w =
      r * fderiv ℝ ψ (r • (w : ℂ)) Complex.I -
        angularTestDeriv (fun z => scaledAngularTest ψ r z * z.re) w := by
  rw [angularTestDeriv_scaled_mul (H := Complex.re) hψ
      Complex.reCLM.contDiff,
    angularTestDeriv_re, map_smul,
    circle_frame_apply_I (fderiv ℝ ψ (r • (w : ℂ))) w]
  change _ = r * ((w : ℂ).im * _ + (w : ℂ).re * _) -
    (ψ (r • (w : ℂ)) * -(w : ℂ).im + (w : ℂ).re * (r * _))
  ring

end KsIndex.Trace
