module

public import KsIndexLean.PaperSlitBoundedApproximation
public import KsIndexLean.VerticalWeakGreen

@[expose] public section


/-! Puncture removal for weak tests in every real-phase slit sector. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1

/-- Vanishing against endpoint-avoiding tests implies vanishing against all
sector tests. No rationality or cyclic-closure assumption on the phase is needed. -/
theorem paperSlit_puncture_removal (α : ℝ) (j : ℕ)
    (u : paperSlitCharacterDomain α j)
    (h : ∀ v : paperSlitCharacterDomain α j,
      (∃ ρ : ℝ, 0 < ρ ∧
        (∀ᵐ z ∂volume.restrict disk,
          (∃ p ∈ Surface.punctures 3, ‖z-p‖ ≤ ρ) → valueCLM v.val.1 z = 0) ∧
        (∀ᵐ z ∂volume.restrict disk,
          (∃ p ∈ Surface.punctures 3, ‖z-p‖ ≤ ρ) → valueCLM v.val.2 z = 0)) →
      weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
        weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0)
    (v : paperSlitCharacterDomain α j) :
    weakJacobi (surfacePotential 3) u.val.1 v.val.1 +
      weakJacobi (surfacePotential 3) u.val.2 v.val.2 = 0 := by
  classical
  have hex (n : ℕ) := exists_paperSlit_puncture_approx α j v
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose w M ρ hM hρ hw hb1 hb2 hz1 hz2 using hex
  have ht : Tendsto (fun n => (w n).val) atTop (𝓝 v.val) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
      (show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) from
        tendsto_one_div_add_atTop_nhds_zero_nat) ε hε)
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at he
    exact (show dist (w n).val v.val < 1 / ((n : ℝ)+1) by
      simpa only [dist_eq_norm] using hw n).trans he
  have hc : Continuous (fun p : ComplexH1 × ComplexH1 =>
      weakJacobi (surfacePotential 3) u.val.1 p.1 +
        weakJacobi (surfacePotential 3) u.val.2 p.2) :=
    ((continuous_weakJacobi_fixed_left _ _).comp continuous_fst).add
      ((continuous_weakJacobi_fixed_left _ _).comp continuous_snd)
  exact isClosed_eq hc continuous_const |>.mem_of_tendsto ht
    (Eventually.of_forall fun n => h (w n) ⟨ρ n, hρ n, hz1 n, hz2 n⟩)

end KsIndex.Spectral
