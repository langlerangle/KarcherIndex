module

public import KsIndexLean.WeakProjectionOn
public import KsIndexLean.DiskCutoffEnergy

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Real projection of the actual compactly supported extension in Tau Ceti's carrier. -/
def diskExtensionRealH1 (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) :
    W1p (volume : Measure ℂ) ⊤ 2 :=
  projectedH1On L (cutoffDiskExtension_spec u).1
    (by simpa using (cutoffDiskExtension_spec u).2.1)
    (fun d => by simpa using (cutoffDiskExtension_spec u).2.2 d)

lemma diskExtensionRealH1_value_ae (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) :
    W1p.value (diskExtensionRealH1 L u) =ᵐ[volume] fun z => L (cutoffDiskExtension u z) := by
  have h := projectedH1On_value_ae L (cutoffDiskExtension_spec u).1
    (show MemLp (cutoffDiskExtension u) 2 (volume.restrict ((⊤ : Opens ℂ) : Set ℂ)) by
      simpa using (cutoffDiskExtension_spec u).2.1)
    (fun d => by simpa using (cutoffDiskExtension_spec u).2.2 d)
  simpa only [diskExtensionRealH1, Opens.coe_top, Measure.restrict_univ] using h

lemma diskExtensionRealH1_gradient_ae (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) :
    W1p.gradient (diskExtensionRealH1 L u) =ᵐ[volume]
      projectedGradientRaw L (cutoffDiskExtensionJet u) := by
  have h := projectedH1On_gradient_ae L (cutoffDiskExtension_spec u).1
    (show MemLp (cutoffDiskExtension u) 2 (volume.restrict ((⊤ : Opens ℂ) : Set ℂ)) by
      simpa using (cutoffDiskExtension_spec u).2.1)
    (fun d => by simpa using (cutoffDiskExtension_spec u).2.2 d)
  simpa only [diskExtensionRealH1, Opens.coe_top, Measure.restrict_univ] using h

end KsIndex.Trace
