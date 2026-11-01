module

public import KsIndexLean.SphericalCanonicalQuotient

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

lemma stereoAreaDensity_le_four (z : ℂ) : stereoAreaDensity z ≤ 4 := by
  rw [stereoAreaDensity_eq]
  apply (div_le_iff₀ (by positivity : 0 < (1 + ‖z‖ ^ 2) ^ 2)).mpr
  nlinarith [sq_nonneg (‖z‖ ^ 2)]

lemma one_le_stereoAreaDensity_disk {z : ℂ} (hz : z ∈ disk) :
    1 ≤ stereoAreaDensity z := by
  have hn := SurfaceForm.mem_disk_iff.mp hz
  rw [stereoAreaDensity_eq]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖z‖ ^ 2) ^ 2)).mpr
  have hsq : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  nlinarith [sq_nonneg (‖z‖ ^ 2), sq_nonneg (1 - ‖z‖ ^ 2)]

lemma stereoAreaMeasure_disk_le :
    stereoAreaMeasure.restrict (disk : Set ℂ) ≤
      (4 : ℝ≥0∞) • volume.restrict (disk : Set ℂ) := by
  rw [stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet, ← withDensity_const]
  apply withDensity_mono
  filter_upwards with z
  exact (ENNReal.ofReal_le_ofReal (stereoAreaDensity_le_four z)).trans_eq (by norm_num)

lemma volume_disk_le_stereoAreaMeasure :
    volume.restrict (disk : Set ℂ) ≤ stereoAreaMeasure.restrict (disk : Set ℂ) := by
  rw [stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet]
  have h : (volume.restrict (disk : Set ℂ)).withDensity (fun _ => (1 : ℝ≥0∞)) ≤
      (volume.restrict (disk : Set ℂ)).withDensity
        (fun z => ENNReal.ofReal (stereoAreaDensity z)) := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    exact (by norm_num : (1 : ℝ≥0∞) = ENNReal.ofReal 1).trans_le
      (ENNReal.ofReal_le_ofReal (one_le_stereoAreaDensity_disk hz))
  simpa only [withDensity_const, one_smul] using h

lemma memLp_stereoAreaMeasure_disk_iff (f : ℂ → ℂ) (p : ℝ≥0∞) :
    MemLp f p (stereoAreaMeasure.restrict (disk : Set ℂ)) ↔
      MemLp f p (volume.restrict (disk : Set ℂ)) := by
  constructor
  · exact MemLp.mono_measure volume_disk_le_stereoAreaMeasure
  · intro h
    exact h.of_measure_le_smul (by norm_num) stereoAreaMeasure_disk_le

lemma eLpNorm_disk_comparison (f : ℂ → ℂ) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict (disk : Set ℂ)) ≤
      eLpNorm f p (stereoAreaMeasure.restrict (disk : Set ℂ)) ∧
    eLpNorm f p (stereoAreaMeasure.restrict (disk : Set ℂ)) ≤
      (4 : ℝ≥0∞) ^ (1 / p).toReal • eLpNorm f p (volume.restrict (disk : Set ℂ)) :=
  ⟨eLpNorm_mono_measure f volume_disk_le_stereoAreaMeasure,
    eLpNorm_le_of_measure_le_smul stereoAreaMeasure_disk_le⟩

end KsIndex.Spherical
