module

/-
KsIndexLean — BallPolar: polar change of variables over the unit disk.

For continuous `f : ℂ → ℝ`,
  `∫_{|w|<1} f = ∫_0^1 ∫_0^{2π} r · f(r e^{iθ}) dθ dr`   (`setIntegral_ball_polar`),
i.e. the disk integral in "radius-outer, angle-inner over [0,2π]" form, matching the convention
`polarCoord.symm (r,θ) = r e^{iθ}`.

Proof route: Mathlib's `Complex.integral_comp_polarCoord_symm` applied to the ball indicator, the
target restricted to `r < 1`, Fubini (`setIntegral_prod`), and the `(-π,π) → (0,2π)` shift by
`2π`-periodicity of `θ ↦ f(r e^{iθ})`.

Proved by Harmonic's Aristotle from a statement and proof route by Kai.
-/
public import Mathlib

@[expose] public section


noncomputable section

open Complex Real MeasureTheory intervalIntegral

namespace KsIndex.BallPolar

/-- **Polar CoV over the unit disk.**  For continuous `f : ℂ → ℝ`,
`∫_{|w|<1} f = ∫_0^1 ∫_0^{2π} r · f(r e^{iθ}) dθ dr`. -/
theorem setIntegral_ball_polar {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ w in Metric.ball (0 : ℂ) 1, f w
      = ∫ r in (0 : ℝ)..1, ∫ θ in (0 : ℝ)..(2 * π),
          r * f ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) := by
  have hsymm : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p
      = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I) := by
    intro p
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
    simp
  set g : ℝ × ℝ → ℝ := fun p => p.1 * f ((p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)) with hg
  have hgc : Continuous g := by
    apply Continuous.mul continuous_fst
    exact hf.comp (by fun_prop)
  -- Polar change of variables applied to the indicator of the unit ball.
  have h1 : ∫ w in Metric.ball (0 : ℂ) 1, f w
      = ∫ p in polarCoord.target,
          p.1 • (Metric.ball (0 : ℂ) 1).indicator f (Complex.polarCoord.symm p) := by
    rw [Complex.integral_comp_polarCoord_symm,
      MeasureTheory.integral_indicator measurableSet_ball]
  have hsub : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π ⊆ polarCoord.target := by
    rw [polarCoord_target]
    exact Set.prod_mono (fun x hx => hx.1) (fun x hx => hx)
  have hmt : MeasurableSet (polarCoord.target) := by
    rw [polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  have hnorm : ∀ p : ℝ × ℝ, 0 < p.1 → ‖Complex.polarCoord.symm p‖ = p.1 := by
    intro p hp
    rw [hsymm p]
    simp [abs_of_pos hp]
  -- The indicator cuts the target down to `Ioo 0 1 ×ˢ Ioo (-π) π`.
  have h2 : ∫ p in polarCoord.target,
          p.1 • (Metric.ball (0 : ℂ) 1).indicator f (Complex.polarCoord.symm p)
      = ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π, g p := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmt hsub ?_]
    · apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hp
      have hp1 : 0 < p.1 := hp.1.1
      have hmem : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, hnorm p hp1]
        exact hp.1.2
      change p.1 • (Metric.ball (0 : ℂ) 1).indicator f (Complex.polarCoord.symm p) = g p
      rw [Set.indicator_of_mem hmem, hsymm p]
      simp [hg]
    · intro p hp
      obtain ⟨hpt, hps⟩ := hp
      rw [polarCoord_target] at hpt
      have hp1 : 0 < p.1 := hpt.1
      have hnb : Complex.polarCoord.symm p ∉ Metric.ball (0 : ℂ) 1 := by
        simp only [Metric.mem_ball, dist_zero_right, hnorm p hp1, not_lt]
        by_contra h
        exact hps ⟨⟨hp1, not_le.mp h⟩, hpt.2⟩
      rw [Set.indicator_of_notMem hnb]
      simp
  have hint : IntegrableOn g (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π) := by
    apply IntegrableOn.mono_set (t := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-π) π)
    · exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) hgc.continuousOn
    · exact Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
  -- Fubini.
  have h3 : ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-π) π, g p
      = ∫ r in Set.Ioo (0 : ℝ) 1, ∫ θ in Set.Ioo (-π) π, g (r, θ) :=
    setIntegral_prod g hint
  -- The angular integrand is `2π`-periodic, so `(0, 2π)` may replace `(-π, π)`.
  have hper : ∀ r : ℝ, Function.Periodic (fun θ : ℝ => g (r, θ)) (2 * π) := by
    intro r θ
    simp only [hg]
    norm_cast
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    norm_num [Complex.exp_two_pi_mul_I]
  have hinner : ∀ r : ℝ, ∫ θ in (0 : ℝ)..(2 * π), g (r, θ)
      = ∫ θ in Set.Ioo (-π) π, g (r, θ) := by
    intro r
    have hshift := (hper r).intervalIntegral_add_eq (-π) 0
    rw [show (0 : ℝ) + 2 * π = 2 * π by ring, show -π + 2 * π = π by ring] at hshift
    rw [← hshift, intervalIntegral.integral_of_le (by linarith [pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  rw [h1, h2, h3, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo fun r _ => (hinner r).symm

end KsIndex.BallPolar
