module

public import KsIndexLean.InversionDerivative

@[expose] public section


open MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma joinedDiskAngular_reflection (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    joinedDiskAngular u v c (KsIndex.Bracket.σ z) = c • joinedDiskAngular v u c⁻¹ z := by
  simp only [joinedDiskAngular, radialJoin, radialInversion_eq_sigma, KsIndex.Bracket.σ_σ]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (KsIndex.Bracket.not_norm_σ_le hz h), ite_eq_left h.le]
  · have hi : ‖KsIndex.Bracket.σ z‖ ≤ 1 := by
      rw [KsIndex.Bracket.norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h), smul_smul, mul_inv_cancel₀ hc, one_smul]

lemma joinedDiskRadial_reflection (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    -(‖KsIndex.Bracket.σ z‖ • joinedDiskRadial u v c (KsIndex.Bracket.σ z)) =
      c • (‖z‖ • joinedDiskRadial v u c⁻¹ z) := by
  have hr : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  simp only [joinedDiskRadial, radialJoin, invertedRadialField,
    radialInversion_eq_sigma, KsIndex.Bracket.σ_σ]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (KsIndex.Bracket.not_norm_σ_le hz h), ite_eq_left h.le]
    simp only [KsIndex.Bracket.norm_σ, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_pow]
    field_simp
  · have hi : ‖KsIndex.Bracket.σ z‖ ≤ 1 := by
      rw [KsIndex.Bracket.norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h)]
    simp only [KsIndex.Bracket.norm_σ, Complex.real_smul, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_pow]
    field_simp

lemma joinedDiskJet_reflection (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    (joinedDiskJet u v c (KsIndex.Bracket.σ z)).comp (fderiv ℝ KsIndex.Bracket.σ z) =
      c • joinedDiskJet v u c⁻¹ z := by
  have hs : KsIndex.Bracket.σ z ≠ 0 := by simp [KsIndex.Bracket.σ, hz]
  apply clm_eq_of_radial_rotation hz
  · simp only [ContinuousLinearMap.comp_apply, smul_apply,
      fderiv_sigma_radial hz, map_neg, joinedDiskJet,
      reconstructedJet_radial _ _ hs, reconstructedJet_radial _ _ hz]
    exact joinedDiskRadial_reflection u v hc hz hn
  · simp only [ContinuousLinearMap.comp_apply, smul_apply,
      fderiv_sigma_rotation hz, joinedDiskJet,
      reconstructedJet_rotation _ _ hs, reconstructedJet_rotation _ _ hz]
    exact joinedDiskAngular_reflection u v hc hz hn

lemma joinedDiskJet_reflection_ae (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) :
    (fun z => (joinedDiskJet u v c (KsIndex.Bracket.σ z)).comp
      (fderiv ℝ KsIndex.Bracket.σ z)) =ᵐ[volume] (fun z => c • joinedDiskJet v u c⁻¹ z) := by
  filter_upwards [volume.ae_ne (0 : ℂ), ae_norm_ne_one] with z hz hn
  exact joinedDiskJet_reflection u v hc hz hn

end KsIndex.Trace
