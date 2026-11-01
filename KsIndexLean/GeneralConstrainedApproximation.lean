module

public import KsIndexLean.RadialCharacter
public import KsIndexLean.ConstrainedPunctureApproximation

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Bounded values are dense within the actual mixed paper-character domain. -/
theorem exists_mixed_character_bounded_approx (k r : ℕ) (b1 b0 : Bool) (u : ComplexH1)
    (hu : u ∈ mixedCharacterDomain k r b1 b0) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ComplexH1, ∃ M : ℝ, v ∈ mixedCharacterDomain k r b1 b0 ∧ 0 < M ∧
      ‖v - u‖ < ε ∧ ∀ᵐ z ∂volume.restrict disk, ‖valueCLM v z‖ ≤ M := by
  have ht (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hc := diskRadial_tendsto (fun n => (ht n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat u
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hc ε hε).exists
  refine ⟨diskRadial _ (ht n).le u, (Real.sqrt (1 / ((n : ℝ) + 1)))⁻¹,
    diskRadial_mem_mixedCharacterDomain _ (ht n).le k r b1 b0 hu,
    inv_pos.mpr (Real.sqrt_pos.mpr (ht n)), ?_, diskRadial_bounded (ht n) u⟩
  simpa only [dist_eq_norm] using hn

/-- Puncture-avoiding bounded approximation for every member of the mixed-character domain,
with no bounded-value assumption on the input. -/
theorem exists_general_mixed_character_puncture_approx {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    (b1 b0 : Bool) (u : ComplexH1) (hu : u ∈ mixedCharacterDomain k r b1 b0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ComplexH1, ∃ M ρ : ℝ, v ∈ mixedCharacterDomain k r b1 b0 ∧
      0 < M ∧ 0 < ρ ∧ ‖v - u‖ < ε ∧
      (∀ᵐ z ∂volume.restrict disk, ‖valueCLM v z‖ ≤ M) ∧
      (∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM v z = 0) := by
  obtain ⟨w, M, hwd, hM, hw, hb⟩ :=
    exists_mixed_character_bounded_approx k r b1 b0 u hu (half_pos hε)
  obtain ⟨v, ρ, hvd, hρ, hv, hvb, hvz⟩ :=
    exists_mixed_character_puncture_approx hk r b1 b0 w hwd hb (half_pos hε)
  refine ⟨v, M, ρ, hvd, hM, hρ, ?_, hvb, hvz⟩
  calc
    ‖v - u‖ = ‖(v - w) + (w - u)‖ := by congr 1; abel
    _ ≤ ‖v - w‖ + ‖w - u‖ := norm_add_le _ _
    _ < ε := by linarith

end KsIndex.Trace
