module

public import KsIndexLean.CollarInversionBound
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.Spherical

lemma map_sigma_collar_le :
    Measure.map σ (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) ≤
      (16 : ℝ≥0∞) • volume.restrict (annulusSet (1 / 2 : ℝ) 2) := by
  apply Measure.le_iff.mpr
  intro s hs
  have hm : Measurable (s.indicator (fun _ : ℂ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hs
  have hh := lintegral_sigma_collar_le _ hm
  rw [← lintegral_map hm measurable_sigma] at hh
  simpa only [lintegral_indicator hs, lintegral_one, Measure.restrict_apply_univ,
    Measure.smul_apply, smul_eq_mul] using hh

lemma memLp_sigma_collar {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))) :
    MemLp (u ∘ σ) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) :=
  (hu.of_measure_le_smul (by norm_num : (16 : ℝ≥0∞) ≠ ⊤) map_sigma_collar_le).comp_of_map
    measurable_sigma.aemeasurable

lemma eLpNorm_sigma_collar_le {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))) :
    eLpNorm (u ∘ σ) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) ≤
      (16 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  have hh := hu.of_measure_le_smul (by norm_num : (16 : ℝ≥0∞) ≠ ⊤) map_sigma_collar_le
  rw [← eLpNorm_map_measure hh.aestronglyMeasurable measurable_sigma.aemeasurable]
  exact eLpNorm_le_of_measure_le_smul map_sigma_collar_le

end KsIndex.Trace
