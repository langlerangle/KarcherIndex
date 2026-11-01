module

public import KsIndexLean.WeakCutoffH1Limit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma diskCutoff_value_vanish_near {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (u : ComplexH1) :
    ∀ᵐ z ∂volume.restrict disk,
      (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ (cutoffEps j) ^ 2) →
        valueCLM (diskCutoff k j u) z = 0 := by
  filter_upwards [diskCutoff_value_ae k j u] with z hz
  intro hp
  rw [hz, cutP_eq_zero hk (cutoffEps_pos j) (cutoffEps_lt_one j) hp, zero_smul]

lemma diskCutoff_value_bound (k j : ℕ) (u : ComplexH1) {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u z‖ ≤ M) :
    ∀ᵐ z ∂volume.restrict disk, ‖valueCLM (diskCutoff k j u) z‖ ≤ M := by
  filter_upwards [diskCutoff_value_ae k j u, hu] with z hz hu
  rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutP_nonneg k (cutoffEps j) z)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (cutP_le_one k (cutoffEps j) z)).trans hu

/-- Bounded weak H1 functions admit arbitrarily close, equally bounded approximants
vanishing in a positive-radius neighborhood of every puncture (relative to the disk). -/
theorem exists_bounded_puncture_approx {k : ℕ} (hk : 1 ≤ k) (u : ComplexH1) {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u z‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ComplexH1, ∃ ρ : ℝ, 0 < ρ ∧ ‖v - u‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM v z = 0) := by
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp (diskCutoff_tendsto_of_bounded hk u hu) ε hε).exists
  refine ⟨diskCutoff k j u, (cutoffEps j) ^ 2, pow_pos (cutoffEps_pos j) 2, ?_,
    diskCutoff_value_bound k j u hu, diskCutoff_value_vanish_near hk j u⟩
  simpa only [dist_eq_norm] using hj

end KsIndex.Trace
