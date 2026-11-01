module

public import KsIndexLean.CollarInversionLimit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma toLp_mono_measure_norm_le {μ ν : Measure ℂ} (hν : ν ≤ μ) {u : ℂ → ℂ}
    (hu : MemLp u 2 μ) : ‖(hu.mono_measure hν).toLp u‖ ≤ ‖hu.toLp u‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact ENNReal.toReal_mono hu.eLpNorm_lt_top.ne (eLpNorm_mono_measure u hν)

lemma toLp_mono_measure_tendsto_zero {μ ν : Measure ℂ} (hν : ν ≤ μ) {u : ℕ → ℂ → ℂ}
    (hu : ∀ n, MemLp (u n) 2 μ)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => ((hu n).mono_measure hν).toLp (u n)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hn : Tendsto (fun n => ‖(hu n).toLp (u n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using ht.norm
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => toLp_mono_measure_norm_le hν (hu n)) hn

/-- Actual strong L2 convergence restricts to any smaller measure. -/
theorem toLp_mono_measure_tendsto {μ ν : Measure ℂ} (hν : ν ≤ μ)
    {u : ℕ → ℂ → ℂ} {v : ℂ → ℂ} (hu : ∀ n, MemLp (u n) 2 μ) (hv : MemLp v 2 μ)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hv.toLp v))) :
    Tendsto (fun n => ((hu n).mono_measure hν).toLp (u n)) atTop
      (𝓝 ((hv.mono_measure hν).toLp v)) := by
  have hd : Tendsto (fun n => ((hu n).sub hv).toLp (u n - v)) atTop (𝓝 0) := by
    have hh := ht.sub_const (hv.toLp v)
    simp only [sub_self] at hh
    exact hh
  exact tendsto_sub_nhds_zero_iff.mp
    (toLp_mono_measure_tendsto_zero hν (fun n => (hu n).sub hv) hd)

end KsIndex.Trace
