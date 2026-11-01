module

public import KsIndexLean.LocalizedMollification
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma toLp_norm_sq {μ : Measure ℂ} {f : ℂ → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂μ := by
  have h : ‖hf.toLp f‖ ^ 2 = ∫ z, ‖hf.toLp f z‖ ^ 2 ∂μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.inner_def (𝕜 := ℝ) (hf.toLp f) (hf.toLp f))
  rw [h]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  rw [hz]

/-- Dominated convergence of raw errors gives convergence in the actual L2 norm. -/
theorem toLp_tendsto_zero_of_dominated {μ : Measure ℂ} {f : ℕ → ℂ → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) {b : ℂ → ℝ}
    (hb : Integrable (fun z => b z ^ 2) μ)
    (hbound : ∀ n, ∀ᵐ z ∂μ, ‖f n z‖ ≤ b z)
    (ht : ∀ᵐ z ∂μ, Tendsto (fun n => f n z) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 0) := by
  have hm n : AEStronglyMeasurable (fun z => ‖f n z‖ ^ 2) μ :=
    (hf n).aestronglyMeasurable.norm.pow 2
  have hbd n : ∀ᵐ z ∂μ, ‖‖f n z‖ ^ 2‖ ≤ b z ^ 2 := by
    filter_upwards [hbound n] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n => ‖f n z‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ht] with z hz
    simpa using hz.norm.pow 2
  have hi := tendsto_integral_of_dominated_convergence (fun z => b z ^ 2) hm hb hbd hlim
  have hsq : Tendsto (fun n => ‖(hf n).toLp (f n)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simp_rw [toLp_norm_sq]
    simpa using hi
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

/-- Strong L2 convergence has an AE convergent subsequence of the original raw functions. -/
theorem exists_ae_subsequence_of_toLp_tendsto {μ : Measure ℂ} {f : ℕ → ℂ → ℂ} {u : ℂ → ℂ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (ht : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂μ, Tendsto (fun n => f (ns n) z) atTop (𝓝 (u z)) := by
  obtain ⟨ns, hns, ha⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  have he : ∀ᵐ z ∂μ, ∀ n, (hf n).toLp (f n) z = f n z :=
    ae_all_iff.mpr (fun n => (hf n).coeFn_toLp)
  filter_upwards [ha, he, hu.coeFn_toLp] with z hz he hu
  simpa only [he, hu] using hz

end KsIndex.Trace
