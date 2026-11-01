module

public import KsIndexLean.CartesianReconstructionFields

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma polarCoefficient_one_circle (L : ℂ →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    polarCoefficient L 1 (r • (w : ℂ)) = L w := by
  have hn : ‖(w : ℂ)‖ = 1 := by simp
  simp only [polarCoefficient, pow_one, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, hn, mul_one, smul_eq_mul]
  field_simp

lemma polarCoefficient_two_circle (L : ℂ →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    polarCoefficient L 2 (r • (w : ℂ)) = L w / r := by
  have hn : ‖(w : ℂ)‖ = 1 := by simp
  simp only [polarCoefficient, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, hn, mul_one, smul_eq_mul]
  field_simp

lemma weighted_reconstruction_X (ψ : ℂ → ℝ) (u v q : ℂ → ℂ)
    {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    r • (fderiv ℝ ψ (r • (w : ℂ)) 1 • u (r • (w : ℂ)) +
      ψ (r • (w : ℂ)) • reconstructedX v q (r • (w : ℂ))) = rawCartesianOne ψ u v q r w := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  rw [reconstructedX, polarCoefficient_one_circle _ hr w, polarCoefficient_two_circle _ hr w]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply,
    rawCartesianOne, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hrC]
  ring

lemma weighted_reconstruction_Y (ψ : ℂ → ℝ) (u v q : ℂ → ℂ)
    {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    r • (fderiv ℝ ψ (r • (w : ℂ)) Complex.I • u (r • (w : ℂ)) +
      ψ (r • (w : ℂ)) • reconstructedY v q (r • (w : ℂ))) = rawCartesianI ψ u v q r w := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  rw [reconstructedY, polarCoefficient_one_circle _ hr w, polarCoefficient_two_circle _ hr w]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply,
    rawCartesianI, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hrC]
  ring

end KsIndex.Trace
