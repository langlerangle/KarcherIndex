module

public import KsIndexLean.OperatorL2Continuity

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma bounded_real_smul_memLp {μ : Measure ℂ} {a : ℂ → ℝ} {u : ℂ → ℂ}
    (ha : AEStronglyMeasurable a μ) (hu : MemLp u 2 μ) {C : ℝ}
    (hb : ∀ᵐ z ∂μ, ‖a z‖ ≤ C) : MemLp (fun z => a z • u z) 2 μ := by
  apply hu.of_le_mul (c := C) (ha.smul hu.aestronglyMeasurable)
  filter_upwards [hb] with z hz
  change ‖a z • u z‖ ≤ C * ‖u z‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

lemma bounded_real_smul_toLp_norm_le {μ : Measure ℂ} {a : ℂ → ℝ} {u : ℂ → ℂ}
    (ha : AEStronglyMeasurable a μ) (hu : MemLp u 2 μ) {C : ℝ}
    (hb : ∀ᵐ z ∂μ, ‖a z‖ ≤ C) :
    ‖(bounded_real_smul_memLp ha hu hb).toLp (fun z => a z • u z)‖ ≤ C * ‖hu.toLp u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(bounded_real_smul_memLp ha hu hb).coeFn_toLp, hu.coeFn_toLp, hb]
    with z hz hu hb
  rw [hz, hu]
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

lemma bounded_real_smul_tendsto_zero {μ : Measure ℂ} {a : ℂ → ℝ} {u : ℕ → ℂ → ℂ}
    (ha : AEStronglyMeasurable a μ) (hu : ∀ n, MemLp (u n) 2 μ) {C : ℝ}
    (hb : ∀ᵐ z ∂μ, ‖a z‖ ≤ C)
    (ht : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => (bounded_real_smul_memLp ha (hu n) hb).toLp
      (fun z => a z • u n z)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hn : Tendsto (fun n => ‖(hu n).toLp (u n)‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using ht.norm
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => bounded_real_smul_toLp_norm_le ha (hu n) hb)
  simpa using hn.const_mul C

end KsIndex.Trace
