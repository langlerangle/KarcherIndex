module

public import KsIndexLean.AngularVariableTests

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma angularTestDeriv_mul {H K : ℂ → ℝ}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hK : ContDiff ℝ (⊤ : ℕ∞) K) (z : ℂ) :
    angularTestDeriv (fun w => H w * K w) z =
      H z * angularTestDeriv K z + K z * angularTestDeriv H z := by
  unfold angularTestDeriv
  rw [fderiv_fun_mul (hH.differentiable (by simp) z) (hK.differentiable (by simp) z)]
  rfl

lemma angularTestDeriv_re (z : ℂ) : angularTestDeriv Complex.re z = -z.im := by
  change fderiv ℝ (Complex.reCLM : ℂ → ℝ) z (z * Complex.I) = _
  rw [Complex.reCLM.hasFDerivAt.fderiv]
  simp

lemma angularTestDeriv_im (z : ℂ) : angularTestDeriv Complex.im z = z.re := by
  change fderiv ℝ (Complex.imCLM : ℂ → ℝ) z (z * Complex.I) = _
  rw [Complex.imCLM.hasFDerivAt.fderiv]
  simp

/-- The angular weak graph can be tested with any smooth coordinate-weighted planar test. -/
theorem circleAngularGraph_weighted_test {F G : Lp ℂ 2 circleMeasure}
    (h : (F, G) ∈ circleAngularGraph) {ψ H : ℂ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (r : ℝ) :
    inner ℂ (angularTestLp
      (angularTestDeriv (fun z => scaledAngularTest ψ r z * H z))
      (contDiff_angularTestDeriv ((contDiff_scaledAngularTest hψ r).mul hH)).continuous) F =
      -inner ℂ (angularTestLp (fun z => scaledAngularTest ψ r z * H z)
        ((contDiff_scaledAngularTest hψ r).mul hH).continuous) G :=
  (mem_circleAngularGraph_iff F G).mp h _ ((contDiff_scaledAngularTest hψ r).mul hH)

/-- The exact derivative includes the derivative of the circle-coordinate multiplier. -/
lemma angularTestDeriv_scaled_mul {ψ H : ℂ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hH : ContDiff ℝ (⊤ : ℕ∞) H) (r : ℝ) (z : ℂ) :
    angularTestDeriv (fun w => scaledAngularTest ψ r w * H w) z =
      ψ (r • z) * angularTestDeriv H z + H z * fderiv ℝ ψ (r • z) (r • (z * Complex.I)) := by
  rw [angularTestDeriv_mul (contDiff_scaledAngularTest hψ r) hH,
    angularTestDeriv_scaled hψ]
  rfl

lemma circle_frame_one (w : Circle₁) :
    (w : ℂ).re • (w : ℂ) - (w : ℂ).im • ((w : ℂ) * Complex.I) = 1 := by
  have hn : ‖(w : ℂ)‖ = 1 := by simp
  have hs := congrArg (fun x : ℝ => x ^ 2) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

lemma circle_frame_I (w : Circle₁) :
    (w : ℂ).im • (w : ℂ) + (w : ℂ).re • ((w : ℂ) * Complex.I) = Complex.I := by
  have hn : ‖(w : ℂ)‖ = 1 := by simp
  have hs := congrArg (fun x : ℝ => x ^ 2) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at hs
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Cartesian derivatives are reconstructed from radial and rotation directions. -/
lemma circle_frame_apply_one (D : ℂ →L[ℝ] ℝ) (w : Circle₁) :
    D 1 = (w : ℂ).re * D w - (w : ℂ).im * D ((w : ℂ) * Complex.I) := by
  conv_lhs => rw [← circle_frame_one w]
  rw [map_sub, map_smul, map_smul]
  rfl

lemma circle_frame_apply_I (D : ℂ →L[ℝ] ℝ) (w : Circle₁) :
    D Complex.I = (w : ℂ).im * D w + (w : ℂ).re * D ((w : ℂ) * Complex.I) := by
  conv_lhs => rw [← circle_frame_I w]
  rw [map_add, map_smul, map_smul]
  rfl

end KsIndex.Trace
