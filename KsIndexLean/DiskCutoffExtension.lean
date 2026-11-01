module

public import KsIndexLean.DiskExtensionEnergy
public import KsIndexLean.WeakH1Localization

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

/-- A fixed cutoff: one through radius one, supported through radius three-halves. -/
def diskExtensionCutoff : ContDiffBump (0 : ℂ) where
  rIn := 1
  rOut := 3 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma diskExtensionCutoff_support :
    tsupport (diskExtensionCutoff : ℂ → ℝ) ⊆ Metric.ball (0 : ℂ) 2 := by
  rw [diskExtensionCutoff.tsupport_eq]
  intro z hz
  have h : dist z 0 ≤ 3 / 2 := hz
  exact show dist z 0 < 2 by linarith

def cutoffDiskExtension (u : ComplexH1) (z : ℂ) : ℂ :=
  diskExtensionCutoff z • refl 1 (valueCLM u) z

def cutoffDiskExtensionJet (u : ComplexH1) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  diskExtensionCutoff z • diskExtensionJet u z +
    (fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z).smulRight (refl 1 (valueCLM u) z)

/-- Compactly supported whole-plane weak extension of an arbitrary disk H1 function. -/
theorem cutoffDiskExtension_spec (u : ComplexH1) :
    TauCeti.HasWeakFDerivOn volume ⊤ (cutoffDiskExtension u) (cutoffDiskExtensionJet u) ∧
      MemLp (cutoffDiskExtension u) 2 volume ∧
      ∀ d, MemLp (fun z => cutoffDiskExtensionJet u z d) 2 volume := by
  apply weakH1_localization diskExtensionCutoff.contDiff diskExtensionCutoff.hasCompactSupport
    (Ω := disk ⊔ annulusOpens (1 / 2) 2)
  · rw [disk_union_reflection_annulus]
    exact diskExtensionCutoff_support
  · exact disk_reflection_extension_weak u
  · simpa only [disk_union_reflection_annulus] using diskExtension_value_memLp u
  · intro d
    simpa only [disk_union_reflection_annulus] using diskExtension_direction_memLp u d

lemma cutoffDiskExtension_eq_inner (u : ComplexH1) {z : ℂ} (hz : z ∈ disk) :
    cutoffDiskExtension u z = valueCLM u z := by
  have hn : ‖z‖ < 1 := KsIndex.SurfaceForm.mem_disk_iff.mp hz
  have hc : diskExtensionCutoff z = 1 := diskExtensionCutoff.one_of_mem_closedBall
    (show dist z 0 ≤ diskExtensionCutoff.rIn by simpa only [dist_zero_right, diskExtensionCutoff] using hn.le)
  rw [cutoffDiskExtension, hc, one_smul, full_boundary_even_eq_inner u hn]

lemma cutoffDiskExtension_hasCompactSupport (u : ComplexH1) :
    HasCompactSupport (cutoffDiskExtension u) := diskExtensionCutoff.hasCompactSupport.smul_right

end KsIndex.Trace
