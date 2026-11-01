module

public import KsIndexLean.ComplementarySeamChart
public import KsIndexLean.InversionJetTransition

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

lemma joined_self_value_parity (u : ComplexH1) (s : ℂ) (hs : s ^ 2 = 1) :
    ∀ᵐ z ∂volume, s • joinedDiskValue u u s (σ z) = joinedDiskValue u u s z := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  filter_upwards [phase_join_reflection_ae u u hs0] with z hz
  rw [hz, hi, smul_smul, ← pow_two, hs, one_smul]

lemma joined_self_jet_parity (u : ComplexH1) (s : ℂ) (hs : s ^ 2 = 1) :
    ∀ᵐ z ∂volume, s • (joinedDiskJet u u s (σ z)).comp (fderiv ℝ σ z) =
      joinedDiskJet u u s z := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  filter_upwards [joinedDiskJet_reflection_ae u u hs0] with z hz
  rw [hz, hi, smul_smul, ← pow_two, hs, one_smul]

end KsIndex.Trace
