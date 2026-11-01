module

public import KsIndexLean.DiskExtensionRealization
public import TauCeti.Analysis.Sobolev.Translation
public import TauCeti.Analysis.Sobolev.W1p.Density

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Translation control for each real projection of the unrestricted disk extension.
Whole-space test-function density imposes no boundary condition on the original disk function. -/
lemma diskExtensionReal_translation_le (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) (h : ℂ) :
    eLpNorm (fun z => L (cutoffDiskExtension u (z + h)) - L (cutoffDiskExtension u z))
      2 volume ≤ ‖h‖ₑ * ‖W1p.gradient (diskExtensionRealH1 L u)‖ₑ := by
  have hv := diskExtensionRealH1_value_ae L u
  have ht := hv.comp_tendsto
    (measurePreserving_add_right (volume : Measure ℂ) h).quasiMeasurePreserving.tendsto_ae
  have heq : eLpNorm (fun z => W1p.value (diskExtensionRealH1 L u) (z + h) -
      W1p.value (diskExtensionRealH1 L u) z) 2 volume =
      eLpNorm (fun z => L (cutoffDiskExtension u (z + h)) - L (cutoffDiskExtension u z))
        2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [hv, ht] with z hz htz
    dsimp only [Function.comp_apply] at htz
    rw [hz, htz]
  rw [← heq]
  exact W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient (by norm_num) h
    (W1p.mem_w1p0Submodule_top (by norm_num) _)

end KsIndex.Trace
