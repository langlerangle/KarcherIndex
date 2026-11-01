module

public import KsIndexLean.ReconstructedJetFrame
public import KsIndexLean.JoinedJetUniqueness

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma radialField_apply (U : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) :
    radialField U z = ‖z‖⁻¹ • U z z := by
  rw [realLinear_coordinates (U z) z]
  simp only [radialField, smul_add, smul_smul, div_eq_mul_inv]
  module

lemma reconstructedJet_polar_inverse (U : ℂ → ℂ →L[ℝ] ℂ) {z : ℂ} (hz : z ≠ 0) :
    reconstructedJet (radialField U) (angularField U) z = U z := by
  apply clm_eq_of_radial_rotation hz
  · rw [reconstructedJet_radial _ _ hz, radialField_apply, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
  · rw [reconstructedJet_rotation _ _ hz, angularField_apply]

/-- The disk carrier supplies weak regularity at its center independently of polar formulas. -/
theorem joinedDisk_inner_disk_weak (u v : ComplexH1) (c : ℂ) :
    TauCeti.HasWeakFDerivOn volume disk (joinedDiskValue u v c) (joinedDiskJet u v c) := by
  have h : TauCeti.HasWeakFDerivOn volume disk (valueCLM u) (Dxy (dxLp u) (dyLp u)) :=
    carrier_hasJet u
  apply (h.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    have hn : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hz
    simp [joinedDiskValue, radialJoin, hn.le]
  · have hne := (volume.ae_ne (0 : ℂ)).filter_mono
      (ae_mono (Measure.restrict_le_self (s := (disk : Set ℂ))))
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet, hne] with z hz hzero
    have hn : ‖z‖ < 1 := by simpa [disk, Metric.mem_ball, dist_zero_right] using hz
    have he := reconstructedJet_polar_inverse (Dxy (dxLp u) (dyLp u)) hzero
    simpa only [joinedDiskJet, reconstructedJet, reconstructedX, reconstructedY,
      joinedDiskRadial, joinedDiskAngular, radialJoin, ite_eq_left hn.le,
      diskRadialRaw, diskAngularRaw] using he.symm

end KsIndex.Trace
