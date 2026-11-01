module

public import KsIndexLean.PaperSeamSmooth

@[expose] public section


/-! Seam representatives agree pointwise with the disk representatives on
both open collars. This is the compatibility needed for global smooth gluing. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma inner_collar_subset_seamDomain {A : Set Circle₁} (hA : IsOpen A) :
    annulusSet (1 / 2 : ℝ) 1 ⊆ (seamDomain A hA : Set ℂ) := by
  intro z hz
  refine ⟨⟨hz.1, lt_trans hz.2 (by norm_num)⟩, ?_⟩
  rintro ⟨w, _, hw⟩
  have hn := mem_sphere_zero_iff_norm.mp w.property
  rw [hw] at hn
  linarith [hz.2]

lemma outer_collar_subset_seamDomain {A : Set Circle₁} (hA : IsOpen A) :
    annulusSet (1 : ℝ) 2 ⊆ (seamDomain A hA : Set ℂ) := by
  intro z hz
  refine ⟨⟨lt_trans (by norm_num) hz.1, hz.2⟩, ?_⟩
  rintro ⟨w, _, hw⟩
  have hn := mem_sphere_zero_iff_norm.mp w.property
  rw [hw] at hn
  linarith [hz.1]

/-- The arbitrary choice of a smooth seam representative does not change its
inner values: they equal the chosen smooth disk representative everywhere. -/
lemma seam_representative_eq_inner {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) {F f : ℂ → ℂ}
    (hF : ContinuousOn F (seamDomain A hA : Set ℂ))
    (hf : ContinuousOn f (WeakH1.disk : Set ℂ))
    (hFa : joinedDiskValue u v c =ᵐ[volume.restrict (seamDomain A hA : Set ℂ)] F)
    (hfa : valueCLM u =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] f) :
    EqOn F f (annulusSet (1 / 2 : ℝ) 1) := by
  have hsub := inner_collar_subset_seamDomain hA
  have ha := hFa.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  apply Measure.eqOn_open_of_ae_eq
    (ha.symm.trans (joinedDiskValue_inner_representative u v c hfa))
    (annulusOpens (1 / 2) 1).isOpen (hF.mono hsub)
  apply hf.mono
  intro z hz
  exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hz.2)

/-- On the outer collar the exact field value is `c * g (σ z)`, with no
conjugation of `c`; conjugation belongs only to the sesquilinear pairing. -/
lemma seam_representative_eq_outer {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) {F g : ℂ → ℂ}
    (hF : ContinuousOn F (seamDomain A hA : Set ℂ))
    (hg : ContinuousOn g (WeakH1.disk : Set ℂ))
    (hFa : joinedDiskValue u v c =ᵐ[volume.restrict (seamDomain A hA : Set ℂ)] F)
    (hga : valueCLM v =ᵐ[volume.restrict (WeakH1.disk : Set ℂ)] g) :
    EqOn F (fun z => c * g (Bracket.σ z)) (annulusSet 1 2) := by
  have hsub := outer_collar_subset_seamDomain hA
  have ha := hFa.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  apply Measure.eqOn_open_of_ae_eq
    (ha.symm.trans (joinedDiskValue_outer_representative u v c hga))
    (annulusOpens 1 2).isOpen (hF.mono hsub)
  apply continuousOn_const.mul
  apply hg.comp
  · intro z hz
    exact (Bracket.contDiffAt_σ
      (norm_pos_iff.mp (lt_trans zero_lt_one hz.1))).continuousAt.continuousWithinAt
  · intro z hz
    exact sigma_mem_disk_of_one_lt_norm hz.1

end KsIndex.Trace
