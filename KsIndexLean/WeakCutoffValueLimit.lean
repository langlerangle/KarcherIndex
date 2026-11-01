module

public import KsIndexLean.WeakDiskCutoff

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma diskCutoff_value_error_norm_sq (k j : ℕ) (u : ComplexH1) :
    ‖valueCLM (diskCutoff k j u) - valueCLM u‖ ^ 2 =
      ∫ z in disk, (1 - cutP k (cutoffEps j) z) ^ 2 * ‖valueCLM u z‖ ^ 2 := by
  rw [lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (valueCLM (diskCutoff k j u)) (valueCLM u),
    diskCutoff_value_ae k j u] with z hs hv
  change ‖(valueCLM (diskCutoff k j u) - valueCLM u) z‖ ^ 2 = _
  rw [hs]
  change ‖valueCLM (diskCutoff k j u) z - valueCLM u z‖ ^ 2 = _
  rw [hv]
  have he : cutP k (cutoffEps j) z • valueCLM u z - valueCLM u z =
      (cutP k (cutoffEps j) z - 1) • valueCLM u z := by module
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Cutoffs converge in L2 value for every weak H1 function, without a bounded-value assumption. -/
lemma diskCutoff_value_tendsto {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1) :
    Tendsto (fun j => valueCLM (diskCutoff k j u)) atTop (𝓝 (valueCLM u)) := by
  have hi : IntegrableOn (fun z => ‖valueCLM u z‖ ^ 2) disk :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp (valueCLM u)).aestronglyMeasurable).mp
      (Lp.memLp (valueCLM u))
  have ht := cutoff_weighted_error_tendsto_zero hk hi
  have hsq : Tendsto (fun j => ‖valueCLM (diskCutoff k j u) - valueCLM u‖ ^ 2)
      atTop (𝓝 0) := by
    simp_rw [diskCutoff_value_error_norm_sq]
    exact ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

end KsIndex.Trace
