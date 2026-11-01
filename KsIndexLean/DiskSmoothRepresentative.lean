module

public import KsIndexLean.GeneralDiskClassical

@[expose] public section


/-!
# Derivatives of a smooth disk representative

If a smooth function on the open disk agrees almost everywhere with the value
of a `ComplexH1` field, its real derivatives in directions `1` and `Complex.I`
agree almost everywhere with that field's weak coordinate derivatives.
Weak-derivative uniqueness identifies the full derivative before evaluation
in the two coordinate directions. All conclusions are restricted to the disk.
-/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Weq
open KsIndex.WeakH1

theorem disk_smooth_representative_derivatives (u : ComplexH1) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (disk : Set ℂ))
    (ha : valueCLM u =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    dxCLM u =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ f z 1) ∧
    dyCLM u =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ f z Complex.I) := by
  have hw := (carrier_hasJet u).congr_ae ha
  have he := hw.ae_eq_fderiv
    ((hf.continuousOn_fderiv_of_isOpen disk.isOpen (by simp)).locallyIntegrableOn
      disk.isOpen.measurableSet)
    (fun z hz => (hf.contDiffAt (disk.isOpen.mem_nhds hz)).differentiableAt (by simp))
  constructor
  · change dxLp u =ᵐ[volume.restrict (disk : Set ℂ)] _
    filter_upwards [he] with z hz
    simpa only [Dxy_one] using congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hz
  · change dyLp u =ᵐ[volume.restrict (disk : Set ℂ)] _
    filter_upwards [he] with z hz
    simpa only [Dxy_I] using congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) hz

end KsIndex.Weq
