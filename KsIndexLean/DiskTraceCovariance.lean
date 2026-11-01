module

public import KsIndexLean.DiskH1RotationIsometry
public import KsIndexLean.DiskTraceAgreement
public import KsIndexLean.RadialRotation

@[expose] public section


open Set MeasureTheory

namespace KsIndex.Trace
open KsIndex.WeakH1

lemma diskRotation_value_ae (θ : ℝ) (u : ComplexH1) :
    (valueCLM (diskRotation θ u) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
      (valueCLM u : ℂ → ℂ) ∘ planeRotation θ := by
  change (valueCLM (diskH1Rotation θ u) : ℂ → ℂ) =ᵐ[_] _
  rw [diskH1Rotation_value]
  exact diskLpRotation_coe_ae θ (valueCLM u)

lemma diskProfile_rotation_ae (θ : ℝ) (u : ComplexH1) :
    (fun t => boundaryRotation θ (diskProfile u t)) =ᵐ[volume.restrict (Ioo (1 / 2 : ℝ) 1)]
      diskProfile (diskRotation θ u) := by
  apply radialProfiles_rotation_ae θ
    (sliceLp_coe_ae (by norm_num) (collar_memLp (valueCLM u)))
  have h := diskProfile_ae_slices_of_value (diskRotation_value_ae θ u)
  exact h

/-- Taking the genuine weak trace commutes with same-sign rotation. -/
theorem diskTrace_rotation (θ : ℝ) (u : ComplexH1) :
    diskTraceCLM (diskRotation θ u) = boundaryRotation θ (diskTraceCLM u) :=
  representative_boundaryRotation (by norm_num) θ
    (disk_weak_polar u).2.2 (disk_weak_polar u).2.1
    (disk_weak_polar (diskRotation θ u)).2.2 (disk_weak_polar (diskRotation θ u)).2.1
    (diskProfile_rotation_ae θ u)

theorem diskTrace_rotation_comp (θ : ℝ) :
    diskTraceCLM.comp (diskRotation θ).toContinuousLinearMap =
      (boundaryRotation θ).toContinuousLinearMap.comp diskTraceCLM := by
  apply ContinuousLinearMap.ext
  intro u
  exact diskTrace_rotation θ u

end KsIndex.Trace
