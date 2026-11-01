module

public import KsIndexLean.CollarInversionLp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

lemma toLp_sigma_collar_norm_le {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))) :
    ‖(memLp_sigma_collar hu).toLp (u ∘ σ)‖ ≤
      ((16 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal * ‖hu.toLp u‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp, ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono _ (eLpNorm_sigma_collar_le hu)
  exact ENNReal.mul_ne_top (by finiteness) hu.eLpNorm_lt_top.ne

lemma toLp_sigma_collar_tendsto_zero {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => (memLp_sigma_collar (hu n)).toLp (u n ∘ σ)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hn : Tendsto (fun n => ‖(hu n).toLp (u n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using ht.norm
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => toLp_sigma_collar_norm_le (hu n))
  simpa using hn.const_mul (((16 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal).toReal)

/-- Actual strong L2 convergence is preserved by inversion on the fixed symmetric collar. -/
theorem toLp_sigma_collar_tendsto {u : ℕ → ℂ → ℂ} {v : ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (hv : MemLp v 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v))) :
    Tendsto (fun n => (memLp_sigma_collar (hu n)).toLp (u n ∘ σ)) atTop
      (𝓝 ((memLp_sigma_collar hv).toLp (v ∘ σ))) := by
  have hd : Tendsto (fun n => ((hu n).sub hv).toLp (u n - v)) atTop (𝓝 0) := by
    have h := ht.sub_const (hv.toLp v)
    simp only [sub_self] at h
    exact h
  have hh := toLp_sigma_collar_tendsto_zero (fun n => (hu n).sub hv) hd
  apply tendsto_sub_nhds_zero_iff.mp
  exact hh

end KsIndex.Trace
