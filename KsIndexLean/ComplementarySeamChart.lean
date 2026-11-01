module

public import KsIndexLean.ExtendedSeamEnergy
public import KsIndexLean.SlitInversionCharts

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma arcTrace_swap_phase {A : Set Circle₁} {u v : ComplexH1} {c : ℂ}
    (hc : c ≠ 0) (hm : arcTrace A u = c • arcTrace A v) :
    arcTrace A v = c⁻¹ • arcTrace A u := by
  rw [hm, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem complementarySeamDomain_weak {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) (hm : arcTrace A u = c • arcTrace A v) :
    TauCeti.HasWeakFDerivOn volume (extendedSeamDomain A hA)
      (joinedDiskValue v u c⁻¹) (joinedDiskJet v u c⁻¹) :=
  extendedSeamDomain_weak hA v u c⁻¹ (arcTrace_swap_phase hc hm)

lemma phase_join_reflection (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ ≠ 1) :
    joinedDiskValue u v c (KsIndex.Bracket.σ z) = c • joinedDiskValue v u c⁻¹ z := by
  simp only [joinedDiskValue_sigma_formula, KsIndex.Bracket.σ_σ]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [ite_eq_right (KsIndex.Bracket.not_norm_σ_le hz h), ite_eq_left h.le]
  · have hi : ‖KsIndex.Bracket.σ z‖ ≤ 1 := by
      rw [KsIndex.Bracket.norm_σ]
      exact (inv_le_one₀ (norm_pos_iff.mpr hz)).mpr h.le
    rw [ite_eq_left hi, ite_eq_right (not_le.mpr h), smul_smul, mul_inv_cancel₀ hc, one_smul]

lemma phase_join_reflection_ae (u v : ComplexH1) {c : ℂ} (hc : c ≠ 0) :
    (fun z => joinedDiskValue u v c (KsIndex.Bracket.σ z)) =ᵐ[volume]
      (fun z => c • joinedDiskValue v u c⁻¹ z) := by
  filter_upwards [volume.ae_ne (0 : ℂ), ae_norm_ne_one] with z hz hn
  exact phase_join_reflection u v hc hz hn

end KsIndex.Trace
