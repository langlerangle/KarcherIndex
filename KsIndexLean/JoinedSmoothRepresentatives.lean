module

public import KsIndexLean.SphericalInversionAE
public import KsIndexLean.SlitInversionCharts
public import KsIndexLean.UncutCollarRegions

@[expose] public section


/-! Identify the actual joined Sobolev value and jet with smooth representatives
on each open half-annulus. The outer representative retains the field phase `c`.
No assertion of smoothness across the middle circle is made here. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma sigma_mem_disk_of_one_lt_norm {z : ℂ} (hz : 1 < ‖z‖) :
    Bracket.σ z ∈ (WeakH1.disk : Set ℂ) := by
  apply Metric.mem_ball.mpr
  rw [dist_zero_right, Bracket.norm_σ]
  exact (inv_lt_one₀ (lt_trans zero_lt_one hz)).mpr hz

lemma joinedDiskValue_inner_representative (u v : ComplexH1) (c : ℂ)
    {f : ℂ → ℂ} (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f) :
    joinedDiskValue u v c =ᵐ[volume.restrict (annulusSet (1 / 2) 1)] f := by
  have he := (ae_restrict_iff' WeakH1.disk.isOpen.measurableSet).mp ha
  filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (measurableSet_annulusSet (a := 1 / 2) (b := 1))] with z he hz
  rw [joinedDiskValue_sigma_formula, ite_eq_left hz.2.le]
  exact he (Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2))

lemma joinedDiskValue_outer_representative (u v : ComplexH1) (c : ℂ)
    {g : ℂ → ℂ} (ha : valueCLM v =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g) :
    joinedDiskValue u v c =ᵐ[volume.restrict (annulusSet 1 2)]
      (fun z => c * g (Bracket.σ z)) := by
  have he := Spherical.ae_comp_sigma ((ae_restrict_iff' WeakH1.disk.isOpen.measurableSet).mp ha)
  filter_upwards [he.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (measurableSet_annulusSet (a := 1) (b := 2))] with z he hz
  rw [joinedDiskValue_sigma_formula, ite_eq_right (not_le.mpr hz.1),
    he (sigma_mem_disk_of_one_lt_norm hz.1)]
  rfl

lemma joinedDiskJet_inner_representative (u v : ComplexH1) (c : ℂ)
    {f : ℂ → ℂ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (WeakH1.disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f) :
    joinedDiskJet u v c =ᵐ[volume.restrict (annulusSet (1 / 2) 1)] fderiv ℝ f := by
  have hs : annulusSet (1 / 2 : ℝ) 1 ⊆ (WeakH1.disk : Set ℂ) := by
    intro z hz
    exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2)
  have hsm := hf.mono hs
  have hw := (uncut_inner_collar_weak u v c).congr_ae
    (joinedDiskValue_inner_representative u v c ha)
  exact hw.ae_eq_fderiv
    ((hsm.continuousOn_fderiv_of_isOpen (annulusOpens (1 / 2) 1).isOpen
      (by simp)).locallyIntegrableOn (measurableSet_annulusSet))
    (fun z hz => (hsm.contDiffAt ((annulusOpens (1 / 2) 1).isOpen.mem_nhds hz)).differentiableAt
      (by simp))

lemma joinedDiskJet_outer_representative (u v : ComplexH1) (c : ℂ)
    {g : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (WeakH1.disk : Set ℂ))
    (ha : valueCLM v =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g) :
    joinedDiskJet u v c =ᵐ[volume.restrict (annulusSet 1 2)]
      fderiv ℝ (fun z => c * g (Bracket.σ z)) := by
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => c * g (Bracket.σ z))
      (annulusSet 1 2) := by
    intro z hz
    have hn : z ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hz.1)
    exact (contDiffAt_const.mul
      ((hg.contDiffAt (WeakH1.disk.isOpen.mem_nhds (sigma_mem_disk_of_one_lt_norm hz.1))).comp z
        (Bracket.contDiffAt_σ hn))).contDiffWithinAt
  have hw := (uncut_outer_collar_weak u v c).congr_ae
    (joinedDiskValue_outer_representative u v c ha)
  exact hw.ae_eq_fderiv
    ((hsm.continuousOn_fderiv_of_isOpen (annulusOpens 1 2).isOpen
      (by simp)).locallyIntegrableOn (measurableSet_annulusSet))
    (fun z hz => (hsm.contDiffAt ((annulusOpens 1 2).isOpen.mem_nhds hz)).differentiableAt
      (by simp))

end KsIndex.Trace
