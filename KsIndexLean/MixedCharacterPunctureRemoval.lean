module

public import KsIndexLean.GeneralConstrainedApproximation
public import KsIndexLean.VerticalWeakGreen

@[expose] public section


/-! Puncture removal in mixed weak character domains on the disk. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Tests vanishing near the boundary punctures determine the full weak
Jacobi equation in every mixed character domain. Boundary conditions are
imposed on the weak trace; no pointwise normal derivative is assumed. -/
theorem mixedCharacter_puncture_removal {k : ℕ} (hk : 1 ≤ k)
    (j : ℕ) (b1 b0 : Bool) (V : BoundedRealPotential) (u : ComplexH1)
    (h : ∀ v : mixedCharacterDomain k j b1 b0,
      (∃ ρ : ℝ, 0 < ρ ∧ ∀ᵐ z ∂volume.restrict disk,
        (∃ p ∈ Surface.punctures k, ‖z - p‖ ≤ ρ) → valueCLM v.val z = 0) →
      weakJacobi V u v.val = 0)
    (v : mixedCharacterDomain k j b1 b0) : weakJacobi V u v.val = 0 := by
  classical
  have hex (n : ℕ) := exists_general_mixed_character_puncture_approx hk j b1 b0
    v.val v.property (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose w M ρ hd hM hρ hw hb hz using hex
  have ht : Tendsto w atTop (𝓝 v.val) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
      (show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) from
        tendsto_one_div_add_atTop_nhds_zero_nat) ε hε)
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at he
    exact (show dist (w n) v.val < 1 / ((n : ℝ) + 1) by
      simpa only [dist_eq_norm] using hw n).trans he
  exact isClosed_eq (continuous_weakJacobi_fixed_left V u) continuous_const
    |>.mem_of_tendsto ht
      (Eventually.of_forall fun n => h ⟨w n, hd n⟩ ⟨ρ n, hρ n, hz n⟩)

end KsIndex.Trace
