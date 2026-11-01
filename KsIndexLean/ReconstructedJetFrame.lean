module

public import KsIndexLean.ReconstructedRadialField

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

lemma clm_eq_of_radial_rotation {z : ℂ} (hz : z ≠ 0) {L M : ℂ →L[ℝ] ℂ}
    (hr : L z = M z) (ht : L (z * Complex.I) = M (z * Complex.I)) : L = M := by
  ext d
  have he : d = (d / z).re • z + (d / z).im • (z * Complex.I) := by
    calc
      d = z * (d / z) := by field_simp
      _ = _ := by
        conv_lhs => rw [← Complex.re_add_im (d / z)]
        simp only [Complex.real_smul]
        ring
  rw [he, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hr, ht]

lemma reconstructedJet_radial (v q : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    reconstructedJet v q z z = ‖z‖ • v z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hs : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : z.re * (z.re / ‖z‖) + z.im * (z.im / ‖z‖) = ‖z‖ := by
    field_simp
    nlinarith [hs]
  have h0 : -(z.re * (z.im / ‖z‖ ^ 2)) + z.im * (z.re / ‖z‖ ^ 2) = 0 := by ring
  have he : reconstructedJet v q z z =
      (z.re * (z.re / ‖z‖) + z.im * (z.im / ‖z‖)) • v z +
      (-(z.re * (z.im / ‖z‖ ^ 2)) + z.im * (z.re / ‖z‖ ^ 2)) • q z := by
    simp only [reconstructedJet, add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, reconstructedX, reconstructedY,
      polarCoefficient, pow_one]
    module
  rw [he, h1, h0, zero_smul, add_zero]

lemma reconstructedJet_rotation (v q : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    reconstructedJet v q z (z * Complex.I) = q z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hs : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : z.im * (z.im / ‖z‖ ^ 2) + z.re * (z.re / ‖z‖ ^ 2) = 1 := by
    field_simp
    nlinarith [hs]
  have h0 : -(z.im * (z.re / ‖z‖)) + z.re * (z.im / ‖z‖) = 0 := by ring
  have he : reconstructedJet v q z (z * Complex.I) =
      (-(z.im * (z.re / ‖z‖)) + z.re * (z.im / ‖z‖)) • v z +
      (z.im * (z.im / ‖z‖ ^ 2) + z.re * (z.re / ‖z‖ ^ 2)) • q z := by
    simp only [reconstructedJet, add_apply, ContinuousLinearMap.smulRight_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, add_zero,
      reconstructedX, reconstructedY, polarCoefficient, pow_one]
    module
  rw [he, h1, h0, zero_smul, one_smul, zero_add]

end KsIndex.Trace
