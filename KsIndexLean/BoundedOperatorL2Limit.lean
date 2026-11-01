module

public import KsIndexLean.DominatedL2Limit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

lemma operator_apply_aestronglyMeasurable {μ : Measure ℂ}
    {A : ℂ → ℂ →L[ℝ] ℂ} {g : ℂ → ℂ}
    (hA : AEStronglyMeasurable A μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun z => A z (g z)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hA.prodMk hg)

lemma bounded_operator_memLp {μ : Measure ℂ} {A : ℂ → ℂ →L[ℝ] ℂ} {g : ℂ → ℂ}
    (hA : AEStronglyMeasurable A μ) (hg : MemLp g 2 μ) {C : ℝ}
    (hb : ∀ᵐ z ∂μ, ‖A z‖ ≤ C) : MemLp (fun z => A z (g z)) 2 μ := by
  apply hg.of_le_mul (c := C) (operator_apply_aestronglyMeasurable hA hg.aestronglyMeasurable)
  filter_upwards [hb] with z hz
  exact (A z).le_opNorm (g z) |>.trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))

/-- A uniformly bounded operator field converging AE may be applied to a fixed L2 function;
the resulting error converges strongly to zero. -/
theorem operator_error_tendsto_zero {μ : Measure ℂ}
    {A : ℕ → ℂ → ℂ →L[ℝ] ℂ} {B : ℂ → ℂ →L[ℝ] ℂ} {g : ℂ → ℂ}
    (hA : ∀ n, AEStronglyMeasurable (A n) μ) (hB : AEStronglyMeasurable B μ)
    (hg : MemLp g 2 μ) {C : ℝ}
    (ha : ∀ n, ∀ᵐ z ∂μ, ‖A n z‖ ≤ C) (hb : ∀ᵐ z ∂μ, ‖B z‖ ≤ C)
    (ht : ∀ᵐ z ∂μ, Tendsto (fun n => A n z) atTop (𝓝 (B z))) :
    ∃ he : ∀ n, MemLp (fun z => (A n z - B z) (g z)) 2 μ,
      Tendsto (fun n => (he n).toLp (fun z => (A n z - B z) (g z))) atTop (𝓝 0) := by
  have hnorm n : ∀ᵐ z ∂μ, ‖A n z - B z‖ ≤ 2 * C := by
    filter_upwards [ha n, hb] with z hz hw
    calc
      ‖A n z - B z‖ ≤ ‖A n z‖ + ‖B z‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith
  let he := fun n => bounded_operator_memLp ((hA n).sub hB) hg (hnorm n)
  refine ⟨he, toLp_tendsto_zero_of_dominated he (b := fun z => (2 * C) * ‖g z‖) ?_ ?_ ?_⟩
  · have hi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    have he : (fun z => ((2 * C) * ‖g z‖) ^ 2) =
        (fun z => (2 * C) ^ 2 * ‖g z‖ ^ 2) := by
      funext z
      ring
    rw [he]
    exact hi.const_mul ((2 * C) ^ 2)
  · intro n
    filter_upwards [hnorm n] with z hz
    exact (A n z - B z).le_opNorm (g z) |>.trans
      (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
  · filter_upwards [ht] with z hz
    have hcont : Continuous (fun p : (ℂ →L[ℝ] ℂ) × ℂ => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have hz' : Tendsto (fun n => A n z - B z) atTop (𝓝 0) := by
      simpa only [sub_self] using hz.sub_const (B z)
    have h := (hcont.tendsto (0, g z)).comp
      (hz'.prodMk_nhds tendsto_const_nhds)
    simp only [Function.comp_def] at h
    exact h

end KsIndex.Trace
