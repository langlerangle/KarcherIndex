module

public import KsIndexLean.ReconstructedRadialField
public import KsIndexLean.CutoffRadialNecessity
public import KsIndexLean.CutoffDiskReconstruction

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Planar weak regularity of the explicit cutoff gluing forces genuine cutoff trace matching. -/
theorem cutoff_trace_eq_of_planar_weak {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ)
    (hw : TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 2) (cutoffDiskValue η u v c)
      (reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c))) :
    circleMul (realCircleMap η hη.continuous) (diskTraceCLM u) =
      circleMul (realCircleMap η hη.continuous) (c • diskTraceCLM v) := by
  have hJ := memLp_cutoffDisk_jet hη u v c
  have hp := (weak_polar_pullback (by norm_num) (by norm_num) hw
    (memLp_cutoffDiskValue hη.continuous u v c)
    (hJ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ 1))
    (hJ.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℂ Complex.I))).2.2
  have he := sliceLp_congr_ae (by norm_num : (0 : ℝ) < 1 / 2)
    (radialField_reconstructedJet_ae (b := 2) (by norm_num : (0 : ℝ) < 1 / 2)
      (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c))
  have hr := hp.congr_ae_deriv he
  have hv := slice_cutoffDiskValue hη.continuous u v c
  have hd := slice_cutoffDiskRadial hη.continuous u v c
  have hj := (hr.congr_ae hv).congr_ae_deriv hd
  apply cutoff_trace_eq_of_radial_weak _ u v c
  simp only [joinAt, apply_ite] at hj ⊢
  exact hj

end KsIndex.Trace
