module

public import KsIndexLean.JoinedDiskFields

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

def cutoffDiskValue (η : ℂ → ℝ) (u v : ComplexH1) (c : ℂ) : ℂ → ℂ :=
  angularCutoffField η (joinedDiskValue u v c)

def cutoffDiskRadial (η : ℂ → ℝ) (u v : ComplexH1) (c : ℂ) : ℂ → ℂ :=
  angularCutoffField η (joinedDiskRadial u v c)

def cutoffDiskAngular (η : ℂ → ℝ) (u v : ComplexH1) (c : ℂ) : ℂ → ℂ :=
  fun z => angularCutoffField η (joinedDiskAngular u v c) z +
    angularCutoffField (angularTestDeriv η) (joinedDiskValue u v c) z

lemma memLp_cutoffDiskValue {η : ℂ → ℝ} (hη : Continuous η) (u v : ComplexH1) (c : ℂ) :
    MemLp (cutoffDiskValue η u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  memLp_angularCutoffField (by norm_num) hη (memLp_joinedDiskValue u v c)

lemma memLp_cutoffDiskRadial {η : ℂ → ℝ} (hη : Continuous η) (u v : ComplexH1) (c : ℂ) :
    MemLp (cutoffDiskRadial η u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  memLp_angularCutoffField (by norm_num) hη (memLp_joinedDiskRadial u v c)

lemma memLp_cutoffDiskAngular {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (cutoffDiskAngular η u v c) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  (memLp_angularCutoffField (by norm_num) hη.continuous (memLp_joinedDiskAngular u v c)).add
    (memLp_angularCutoffField (by norm_num) (contDiff_angularTestDeriv hη).continuous
      (memLp_joinedDiskValue u v c))

lemma slice_cutoffDiskValue {η : ℂ → ℝ} (hη : Continuous η) (u v : ComplexH1) (c : ℂ) :
    sliceLp (1 / 2) 2 (cutoffDiskValue η u v c) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 2)]
      (fun r => circleMul (realCircleMap η hη)
        (joinAt 1 (diskProfile u) (fun t => c • diskProfile v t⁻¹) r)) :=
  ae_sliceLp_of_raw_profile (ae_raw_cutoff_profile (by norm_num) hη (raw_joinedDiskValue u v c))

lemma slice_cutoffDiskRadial {η : ℂ → ℝ} (hη : Continuous η) (u v : ComplexH1) (c : ℂ) :
    sliceLp (1 / 2) 2 (cutoffDiskRadial η u v c) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 2)]
      (fun r => circleMul (realCircleMap η hη)
        (joinAt 1 (diskRadialProfile u)
          (fun t => c • invertedRadialDeriv (diskRadialProfile v) t) r)) :=
  ae_sliceLp_of_raw_profile (ae_raw_cutoff_profile (by norm_num) hη (raw_joinedDiskRadial u v c))

lemma slice_cutoffDiskAngular {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) :
    sliceLp (1 / 2) 2 (cutoffDiskAngular η u v c) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 2)]
      (fun r => circleMul (realCircleMap η hη.continuous)
        (joinAt 1 (diskAngularProfile u) (fun t => c • diskAngularProfile v t⁻¹) r) +
        circleMul (realCircleMap (angularTestDeriv η) (contDiff_angularTestDeriv hη).continuous)
          (joinAt 1 (diskProfile u) (fun t => c • diskProfile v t⁻¹) r)) :=
  ae_sliceLp_of_raw_profile (ae_raw_add_profile
    (ae_raw_cutoff_profile (by norm_num) hη.continuous (raw_joinedDiskAngular u v c))
    (ae_raw_cutoff_profile (by norm_num) (contDiff_angularTestDeriv hη).continuous
      (raw_joinedDiskValue u v c)))

end KsIndex.Trace
