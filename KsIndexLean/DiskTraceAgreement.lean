module

public import KsIndexLean.DiskTraceBound

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskProfile_ae_slices_of_value {u : ComplexH1} {f : ℂ → ℂ}
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    ∀ᵐ t ∂volume.restrict (Ioo (1 / 2 : ℝ) 1),
      (diskProfile u t : Circle₁ → ℂ) =ᵐ[circleMeasure] sliceFun f t := by
  have hc := he.filter_mono (ae_mono (Measure.restrict_mono collar_subset_disk le_rfl))
  filter_upwards [sliceLp_coe_ae (by norm_num) (collar_memLp (valueCLM u)),
    ae_slice_ae_eq (by norm_num : (0 : ℝ) < 1 / 2) hc] with t ht hs
  exact ht.trans hs

/-- Agreement holds for any continuous closed-collar representative of the weak class. -/
theorem diskTrace_eq_closedAnnulusProfile {u : ComplexH1} {f : ℂ → ℂ}
    (hf : ContinuousOn f annulus)
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    diskTraceCLM u = closedAnnulusProfile hf 1 :=
  representative_eq_closedAnnulusProfile hf (disk_weak_polar u).2.2
    (disk_weak_polar u).2.1
    (closedAnnulusProfile_ae_eq_of_slices hf (diskProfile_ae_slices_of_value he)) (by norm_num)

theorem diskTrace_coe_ae {u : ComplexH1} {f : ℂ → ℂ}
    (hf : ContinuousOn f annulus)
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure] (fun w => f (w : ℂ)) := by
  rw [diskTrace_eq_closedAnnulusProfile hf he]
  simpa using closedAnnulusProfile_coe_ae hf (t := 1) (by norm_num)

/-- Interior smooth data require a genuine continuous extension to the closed collar. -/
theorem diskTrace_smooth_agreement (F : SmoothH1Data) (hF : ContinuousOn F.F annulus) :
    (diskTraceCLM (smoothToH1 F) : Circle₁ → ℂ) =ᵐ[circleMeasure]
      (fun w => F.F (w : ℂ)) :=
  diskTrace_coe_ae hF (smoothToH1_value_ae F)

end KsIndex.Trace
