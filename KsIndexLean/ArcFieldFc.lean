module

/-
KsIndexLean — Fourier coefficients of the periodic arc field.

For every integer `ℓ`, the periodized half-angle field satisfies
`Parseval.fc vF ℓ = ArcSpace.cC ℓ`. The normalization is
`cC ℓ = g (ℓ + 1/2) / (2π)`, viewed in `ℂ`, where
`TestField.g ξ = 2 * ∫ x in 0..π/2, sqrt (cos x) * cos (ξ*x)`.

Periodicity shifts the Fourier integral from `0..2π` to `-π..π`.
On this closed window the half-angle formula holds, including at `-π`
because the amplitude vanishes there. Reflection pairs the two complex
exponentials into `2*cos ((ℓ+1/2)*x)`. The amplitude vanishes on `π/2..π`,
so the integral reduces to the real cosine integral defining `g`.

This is coefficientwise identification of the uncut field. Cutoff estimates,
weighted summability, and quadratic-form conclusions are separate results.
-/
public import KsIndexLean.ArcField
public import KsIndexLean.Parseval1
public import KsIndexLean.ArcSpace

@[expose] public section


noncomputable section

open Real Set Filter MeasureTheory intervalIntegral Topology

namespace KsIndex.ArcField

/-- `vF` has the half-angle phase on the closed window (`vF(−π) = 0` covers the
endpoint the `toIocMod` window misses). -/
lemma vF_eq_on_Icc {θ : ℝ} (h : θ ∈ Set.Icc (-π) π) :
    vF θ = (hAmp θ : ℂ) * Complex.exp (-Complex.I * (θ : ℂ) / 2) := by
  rcases h.1.eq_or_lt with heq | hlt
  · have hcos : Real.cos θ ≤ 0 := by
      rw [← heq, Real.cos_neg, Real.cos_pi]
      norm_num
    rw [vF_eq_zero_of_nonpos hcos, hAmp_eq_zero_of_nonpos hcos]
    simp
  · exact vF_eq_of_mem ⟨hlt, h.2⟩

/-- The `fc` integrand of `vF` is `2π`-periodic. -/
lemma integrand_periodic (ℓ : ℤ) :
    Function.Periodic
      (fun θ : ℝ => vF θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)) (2 * π) := by
  intro θ
  show vF (θ + 2 * π) * Complex.exp (-(ℓ : ℂ) * Complex.I * ((θ + 2 * π : ℝ) : ℂ))
      = vF θ * Complex.exp (-(ℓ : ℂ) * Complex.I * (θ : ℂ))
  have hexp : Complex.exp (-(ℓ : ℂ) * Complex.I * ((θ + 2 * π : ℝ) : ℂ))
      = Complex.exp (-(ℓ : ℂ) * Complex.I * (θ : ℂ)) := by
    rw [show -(ℓ : ℂ) * Complex.I * ((θ + 2 * π : ℝ) : ℂ)
        = -(ℓ : ℂ) * Complex.I * (θ : ℂ) + ((-ℓ : ℤ) : ℂ) * (2 * (π : ℂ) * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [vF_periodic θ, hexp]

lemma continuous_integrand (ℓ : ℤ) :
    Continuous (fun θ : ℝ => vF θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)) := by
  refine continuous_vF.mul (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul Complex.continuous_ofReal

/-- Window shift: the `fc` integral over `[0, 2π]` equals the one over `[−π, π]`. -/
lemma fc_vF_window (ℓ : ℤ) : Parseval.fc vF ℓ
    = (2 * π : ℝ)⁻¹ * ∫ θ in (-π : ℝ)..π,
        vF θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ) := by
  simp only [Parseval.fc]
  congr 1
  have h := (integrand_periodic ℓ).intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  exact h

/-- On the closed window the integrand collapses to the `(ℓ + 1/2)`-frequency. -/
lemma window_integrand_eq (ℓ : ℤ) {θ : ℝ} (h : θ ∈ Set.Icc (-π) π) :
    vF θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)
      = (hAmp θ : ℂ) * Complex.exp (-(((ℓ : ℂ) + 1/2) * θ) * Complex.I) := by
  rw [vF_eq_on_Icc h, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma continuous_G (ℓ : ℤ) :
    Continuous (fun θ : ℝ =>
      (hAmp θ : ℂ) * Complex.exp (-(((ℓ : ℂ) + 1/2) * θ) * Complex.I)) := by
  refine (Complex.continuous_ofReal.comp continuous_hAmp).mul
    (Complex.continuous_exp.comp ?_)
  refine (continuous_const.mul ?_).neg.mul continuous_const
  exact Complex.continuous_ofReal

/-- Fold `∫_{−π}^π` to `∫_0^π`: `hAmp` is even, the two exponentials combine to `2cos`. -/
lemma window_fold (ℓ : ℤ) :
    (∫ θ in (-π : ℝ)..π,
        (hAmp θ : ℂ) * Complex.exp (-(((ℓ : ℂ) + 1/2) * θ) * Complex.I))
      = ∫ x in (0 : ℝ)..π, (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)) := by
  have hGc := continuous_G ℓ
  set G : ℝ → ℂ :=
    fun θ => (hAmp θ : ℂ) * Complex.exp (-(((ℓ : ℂ) + 1/2) * θ) * Complex.I) with hGdef
  have hsplit : (∫ θ in (-π : ℝ)..π, G θ)
      = (∫ θ in (-π : ℝ)..0, G θ) + ∫ θ in (0 : ℝ)..π, G θ :=
    (integral_add_adjacent_intervals
      (hGc.intervalIntegrable _ _) (hGc.intervalIntegrable _ _)).symm
  have hneg : (∫ θ in (-π : ℝ)..0, G θ) = ∫ x in (0 : ℝ)..π, G (-x) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) (f := G)
    rw [neg_zero] at h
    exact h.symm
  have hpt : ∀ x : ℝ, G (-x) + G x
      = (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)) := by
    intro x
    simp only [hGdef]
    rw [hAmp_even x]
    rw [show -(((ℓ : ℂ) + 1/2) * ((-x : ℝ) : ℂ)) * Complex.I
        = (((ℓ : ℂ) + 1/2) * (x : ℂ)) * Complex.I by push_cast; ring]
    rw [← mul_add, ← Complex.two_cos]
  have hadd : (∫ x in (0 : ℝ)..π, G (-x)) + (∫ x in (0 : ℝ)..π, G x)
      = ∫ x in (0 : ℝ)..π, (G (-x) + G x) :=
    (integral_add ((hGc.comp continuous_neg).intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)).symm
  rw [hsplit, hneg, hadd]
  exact intervalIntegral.integral_congr fun x _ => hpt x

/-- Cut to `[0, π/2]` and realify: the folded integral is exactly `TestField.g (ℓ + 1/2)`, viewed in `ℂ`. -/
lemma fold_cut (ℓ : ℤ) :
    (∫ x in (0 : ℝ)..π, (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)))
      = 2 * ((∫ x in (0 : ℝ)..(π/2),
          Real.sqrt (Real.cos x) * Real.cos (((ℓ : ℝ) + 1/2) * x) : ℝ) : ℂ) := by
  have hπ2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hπ2π : π / 2 ≤ π := by linarith [Real.pi_pos]
  have hHc : Continuous
      (fun x : ℝ => (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x))) := by
    refine (Complex.continuous_ofReal.comp continuous_hAmp).mul
      (continuous_const.mul (Complex.continuous_cos.comp ?_))
    exact continuous_const.mul Complex.continuous_ofReal
  have hsplit : (∫ x in (0 : ℝ)..π, (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)))
      = (∫ x in (0 : ℝ)..(π/2), (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)))
        + ∫ x in (π/2 : ℝ)..π, (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)) :=
    (integral_add_adjacent_intervals
      (hHc.intervalIntegrable _ _) (hHc.intervalIntegrable _ _)).symm
  have hzero : (∫ x in (π/2 : ℝ)..π,
      (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x))) = 0 := by
    calc (∫ x in (π/2 : ℝ)..π, (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x)))
        = ∫ _ in (π/2 : ℝ)..π, (0 : ℂ) := by
          refine intervalIntegral.integral_congr fun x hx => ?_
          rw [Set.uIcc_of_le hπ2π] at hx
          have hcos : Real.cos x ≤ 0 :=
            Real.cos_nonpos_of_pi_div_two_le_of_le hx.1 (by linarith [hx.2, Real.pi_pos])
          rw [hAmp_eq_zero_of_nonpos hcos]
          simp
      _ = 0 := intervalIntegral.integral_zero
  have hreal : ∀ x ∈ Set.uIcc (0 : ℝ) (π/2),
      (hAmp x : ℂ) * (2 * Complex.cos (((ℓ : ℂ) + 1/2) * x))
        = ((2 * (Real.sqrt (Real.cos x) * Real.cos (((ℓ : ℝ) + 1/2) * x)) : ℝ) : ℂ) := by
    intro x hx
    rw [Set.uIcc_of_le hπ2] at hx
    have hcos0 : 0 ≤ Real.cos x :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
    rw [hAmp_eq_sqrt hcos0,
      show ((ℓ : ℂ) + 1/2) * (x : ℂ) = (((((ℓ : ℝ) + 1/2) * x : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cos]
    push_cast
    ring
  rw [hsplit, hzero, add_zero, intervalIntegral.integral_congr hreal]
  have hpull : (∫ x in (0 : ℝ)..(π/2),
      ((2 * (Real.sqrt (Real.cos x) * Real.cos (((ℓ : ℝ) + 1/2) * x)) : ℝ) : ℂ))
      = (((∫ x in (0 : ℝ)..(π/2),
          2 * (Real.sqrt (Real.cos x) * Real.cos (((ℓ : ℝ) + 1/2) * x)) : ℝ)) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [hpull, intervalIntegral.integral_const_mul]
  push_cast
  ring

/-- **The Fourier bridge**: the periodized half-angle field has exactly the test-sequence
coefficients — `fc vF ℓ = cC ℓ` for every `ℓ`. -/
theorem fc_vF (ℓ : ℤ) : Parseval.fc vF ℓ = ArcSpace.cC ℓ := by
  have hEq : ∀ θ ∈ Set.uIcc (-π : ℝ) π,
      vF θ * Complex.exp (-(ℓ : ℂ) * Complex.I * θ)
        = (hAmp θ : ℂ) * Complex.exp (-(((ℓ : ℂ) + 1/2) * θ) * Complex.I) := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (-π : ℝ) ≤ π)] at hθ
    exact window_integrand_eq ℓ hθ
  rw [fc_vF_window, intervalIntegral.integral_congr hEq, window_fold, fold_cut,
    ArcSpace.cC_apply]
  simp only [TestField.c, TestField.g]
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end KsIndex.ArcField
