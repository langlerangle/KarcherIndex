module

public import KsIndexLean.CutoffDiskFields
public import KsIndexLean.AnnularWeakReconstruction

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma cutoffDisk_radial_weak {A : Set Circle₁} (hA : MeasurableSet A)
    {η : ℂ → ℝ} (hη : Continuous η) (hηA : ∀ w : Circle₁, w ∉ A → η w = 0)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (sliceLp (1 / 2) 2 (cutoffDiskValue η u v c))
      (sliceLp (1 / 2) 2 (cutoffDiskRadial η u v c)) 1 := by
  have hw := disk_cutoff_radial_gluing hA (realCircleMap η hη) hηA u v c hm
  have hv := (slice_cutoffDiskValue hη u v c).symm
  have hr := (slice_cutoffDiskRadial hη u v c).symm
  simp only [joinAt, apply_ite] at hw hv hr
  exact (hw.congr_ae hv).congr_ae_deriv hr

lemma cutoffDisk_angular_weak {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 / 2 : ℝ) 2),
      (sliceLp (1 / 2) 2 (cutoffDiskValue η u v c) r,
        sliceLp (1 / 2) 2 (cutoffDiskAngular η u v c) r) ∈ circleAngularGraph := by
  filter_upwards [disk_cutoff_angular_gluing u v c hη,
    slice_cutoffDiskValue hη.continuous u v c, slice_cutoffDiskAngular hη u v c] with r hr hv hq
  rw [hv, hq]
  simpa only [joinAt, apply_ite] using hr

/-- Cutoff two-disk gluing gives a planar weak derivative when the arc traces
match by the complex scalar `c` and the cutoff vanishes on the rest of the circle. -/
theorem cutoffDisk_weak_reconstruction {A : Set Circle₁} (hA : MeasurableSet A)
    {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηA : ∀ w : Circle₁, w ∉ A → η w = 0)
    (u v : ComplexH1) (c : ℂ) (hm : arcTrace A u = c • arcTrace A v) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 2) (cutoffDiskValue η u v c)
      (reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c)) :=
  annular_weak_reconstruction (by norm_num) (by norm_num)
    (memLp_cutoffDiskValue hη.continuous u v c) (memLp_cutoffDiskRadial hη.continuous u v c)
    (memLp_cutoffDiskAngular hη u v c) (cutoffDisk_radial_weak hA hη.continuous hηA u v c hm)
    (cutoffDisk_angular_weak hη u v c)

lemma memLp_cutoffDisk_jet {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c)) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  memLp_reconstructedJet (by norm_num) (memLp_cutoffDiskRadial hη.continuous u v c)
    (memLp_cutoffDiskAngular hη u v c)

end KsIndex.Trace
