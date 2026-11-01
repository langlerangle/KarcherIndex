module

public import KsIndexLean.CutoffPlanarNecessity

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma cutoff_radial_weak_of_trace_eq (η : C(Circle₁, ℝ)) (u v : ComplexH1) (c : ℂ)
    (hm : circleMul η (diskTraceCLM u) = circleMul η (c • diskTraceCLM v)) :
    TauCeti.HasWeakLineDerivOn volume (intervalOpens (1 / 2) 2)
      (joinAt 1 (fun r => circleMul η (diskProfile u r))
        (fun r => circleMul η (c • diskProfile v r⁻¹)))
      (joinAt 1 (fun r => circleMul η (diskRadialProfile u r))
        (fun r => circleMul η (c • invertedRadialDeriv (diskRadialProfile v) r))) 1 := by
  have hv := invertedProfile_weak (disk_weak_polar v).2.2 (disk_weak_polar v).2.1
  have hg := invertedRadialDeriv_integrable (disk_weak_polar v).2.1
  have hp := weak_deriv_const_smul_complex c hv
  have hq := hg.smul c
  apply weak_joinAt_of_match (by norm_num) (by norm_num)
    (circleMul_weakInterval η (disk_weak_polar u).2.2) (circleMul_weakInterval η hp)
    ⟨(circleMulCLM η).integrable_comp (disk_weak_polar u).2.1.1,
      (circleMulCLM η).integrable_comp (disk_weak_polar u).2.1.2⟩
    ⟨(circleMulCLM η).integrable_comp hq.1, (circleMulCLM η).integrable_comp hq.2⟩
  rw [representative_circleMul (by norm_num) η (disk_weak_polar u).2.2
      (disk_weak_polar u).2.1 (by norm_num),
    representative_circleMul (by norm_num) η hp hq (by norm_num),
    representative_smul_complex (by norm_num) c hv hg (by norm_num), Pi.smul_apply,
    invertedProfile_endpoint (disk_weak_polar v).2.2 (disk_weak_polar v).2.1]
  exact hm

/-- Exact fixed-cutoff planar gluing criterion in terms of genuine disk traces. -/
theorem cutoff_planar_weak_iff_trace_eq {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 2) (cutoffDiskValue η u v c)
      (reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c)) ↔
    circleMul (realCircleMap η hη.continuous) (diskTraceCLM u) =
      circleMul (realCircleMap η hη.continuous) (c • diskTraceCLM v) := by
  constructor
  · exact cutoff_trace_eq_of_planar_weak hη u v c
  · intro hm
    have hr := cutoff_radial_weak_of_trace_eq (realCircleMap η hη.continuous) u v c hm
    have hv := (slice_cutoffDiskValue hη.continuous u v c).symm
    have hd := (slice_cutoffDiskRadial hη.continuous u v c).symm
    simp only [joinAt, apply_ite] at hr hv hd
    exact annular_weak_reconstruction (by norm_num) (by norm_num)
      (memLp_cutoffDiskValue hη.continuous u v c) (memLp_cutoffDiskRadial hη.continuous u v c)
      (memLp_cutoffDiskAngular hη u v c) ((hr.congr_ae hv).congr_ae_deriv hd)
      (cutoffDisk_angular_weak hη u v c)

end KsIndex.Trace
