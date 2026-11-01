module

public import KsIndexLean.AnnularWeakReconstruction

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

lemma radialField_reconstructedJet (v q : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    radialField (reconstructedJet v q) z = v z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hs : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h1 : z.re / ‖z‖ * (z.re / ‖z‖) + z.im / ‖z‖ * (z.im / ‖z‖) = 1 := by
    field_simp
    nlinarith [hs]
  have h0 : -(z.re / ‖z‖ * (z.im / ‖z‖ ^ 2)) +
      z.im / ‖z‖ * (z.re / ‖z‖ ^ 2) = 0 := by ring
  have he : radialField (reconstructedJet v q) z =
      (z.re / ‖z‖ * (z.re / ‖z‖) + z.im / ‖z‖ * (z.im / ‖z‖)) • v z +
      (-(z.re / ‖z‖ * (z.im / ‖z‖ ^ 2)) + z.im / ‖z‖ * (z.re / ‖z‖ ^ 2)) • q z := by
    simp only [radialField, reconstructedJet, add_apply,
      ContinuousLinearMap.smulRight_apply, Complex.reCLM_apply, Complex.imCLM_apply,
      Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, one_smul, zero_smul,
      add_zero, zero_add, reconstructedX, reconstructedY, polarCoefficient, pow_one]
    module
  rw [he, h1, h0, one_smul, zero_smul, add_zero]

lemma radialField_reconstructedJet_ae {a b : ℝ} (ha : 0 < a) (v q : ℂ → ℂ) :
    radialField (reconstructedJet v q) =ᵐ[volume.restrict (annulusSet a b)] v := by
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact radialField_reconstructedJet v q (norm_pos_iff.mp (ha.trans hz.1))

end KsIndex.Trace
