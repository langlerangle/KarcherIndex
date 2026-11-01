module

public import KsIndexLean.CollarInversionBound
public import KsIndexLean.WeakH1Adapter

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.Spherical KsIndex.WeakH1

lemma sigma_outer_mem_disk {z : ℂ} (hz : z ∈ annulusSet (1 : ℝ) 2) : σ z ∈ disk := by
  change dist (σ z) 0 < 1
  rw [dist_zero_right, norm_σ]
  exact inv_lt_one_of_one_lt₀ hz.1

/-- Inversion of the outer annulus has a uniform measure bound by the disk measure. -/
theorem lintegral_sigma_outer_le (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in annulusSet (1 : ℝ) 2, F (σ z) ∂volume) ≤
      16 * ∫⁻ z in (disk : Set ℂ), F z ∂volume := by
  let G := (disk : Set ℂ).indicator F
  have hG : Measurable G := hF.indicator disk.isOpen.measurableSet
  have he : (∫⁻ z in annulusSet (1 : ℝ) 2, F (σ z) ∂volume) =
      ∫⁻ z in annulusSet (1 : ℝ) 2, G (σ z) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    exact (indicator_of_mem (sigma_outer_mem_disk hz) F).symm
  rw [he]
  calc
    _ ≤ ∫⁻ z in annulusSet (1 / 2 : ℝ) 2, G (σ z) ∂volume := by
      apply lintegral_mono_set
      intro z hz
      exact ⟨by linarith [hz.1], hz.2⟩
    _ ≤ 16 * ∫⁻ z in annulusSet (1 / 2 : ℝ) 2, G z ∂volume :=
      lintegral_sigma_collar_le G hG
    _ ≤ 16 * ∫⁻ z in (disk : Set ℂ), F z ∂volume := by
      apply mul_le_mul_right
      calc
        _ ≤ ∫⁻ z, G z ∂volume := lintegral_mono' Measure.restrict_le_self le_rfl
        _ = _ := lintegral_indicator disk.isOpen.measurableSet F

lemma map_sigma_outer_le :
    Measure.map σ (volume.restrict (annulusSet (1 : ℝ) 2)) ≤
      (16 : ℝ≥0∞) • volume.restrict (disk : Set ℂ) := by
  apply Measure.le_iff.mpr
  intro s hs
  have hm : Measurable (s.indicator (fun _ : ℂ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hs
  have hh := lintegral_sigma_outer_le _ hm
  rw [← lintegral_map hm measurable_sigma] at hh
  simpa only [lintegral_indicator hs, lintegral_one, Measure.restrict_apply_univ,
    Measure.smul_apply, smul_eq_mul] using hh

lemma memLp_sigma_outer {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (disk : Set ℂ))) :
    MemLp (f ∘ σ) 2 (volume.restrict (annulusSet (1 : ℝ) 2)) :=
  (hf.of_measure_le_smul (by norm_num : (16 : ℝ≥0∞) ≠ ⊤) map_sigma_outer_le).comp_of_map
    measurable_sigma.aemeasurable

lemma eLpNorm_sigma_outer_le {f : ℂ → ℂ}
    (hf : MemLp f 2 (volume.restrict (disk : Set ℂ))) :
    eLpNorm (f ∘ σ) 2 (volume.restrict (annulusSet (1 : ℝ) 2)) ≤
      (16 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm f 2 (volume.restrict (disk : Set ℂ)) := by
  have hh := hf.of_measure_le_smul (by norm_num : (16 : ℝ≥0∞) ≠ ⊤) map_sigma_outer_le
  rw [← eLpNorm_map_measure hh.aestronglyMeasurable measurable_sigma.aemeasurable]
  exact eLpNorm_le_of_measure_le_smul map_sigma_outer_le

end KsIndex.Trace
