module

public import KsIndexLean.CutoffCharacter

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

/-- Bounded puncture approximation retains the actual mixed trace and paper character conditions. -/
theorem exists_mixed_character_puncture_approx {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (b1 b0 : Bool) (u : ComplexH1) (hd : u ∈ mixedCharacterDomain k r b1 b0) {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u z‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ComplexH1, ∃ ρ : ℝ, v ∈ mixedCharacterDomain k r b1 b0 ∧ 0 < ρ ∧ ‖v - u‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM v z = 0) := by
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp (diskCutoff_tendsto_of_bounded hk u hu) ε hε).exists
  refine ⟨diskCutoff k j u, (cutoffEps j) ^ 2,
    diskCutoff_mem_mixedCharacterDomain hk j r b1 b0 hd, pow_pos (cutoffEps_pos j) 2, ?_,
    diskCutoff_value_bound k j u hu, diskCutoff_value_vanish_near hk j u⟩
  simpa only [dist_eq_norm] using hj

/-- Applying the same scalar cutoff to both bounded disk components converges
in the product H1 norm. Each component has its own almost-everywhere value bound;
slit-phase preservation is a separate domain-membership statement. -/
theorem slitCutoff_tendsto_of_bounded {k : ℕ} (hk : 1 ≤ k) (u : DiskPairH1) {M N : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u.1 z‖ ≤ M)
    (hv : ∀ᵐ z ∂volume.restrict disk, ‖valueCLM u.2 z‖ ≤ N) :
    Tendsto (fun j => (diskCutoff k j u.1, diskCutoff k j u.2)) atTop (𝓝 u) :=
  (diskCutoff_tendsto_of_bounded hk u.1 hu).prodMk_nhds
    (diskCutoff_tendsto_of_bounded hk u.2 hv)

end KsIndex.Trace
