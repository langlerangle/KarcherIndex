module

public import Mathlib.Analysis.Distribution.Sobolev

@[expose] public section


/-! The normalized Bessel operator and the planar elliptic Sobolev gain. -/

noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian

namespace KsIndex.Weq
open TemperedDistribution

theorem besselPotential_two_eq (f : 𝓢'(ℂ, ℂ)) :
    besselPotential ℂ ℂ 2 f = f - ((2 * Real.pi) ^ 2)⁻¹ • Δ f := by
  have hadd : fourierMultiplierCLM ℂ (fun z : ℂ => (1 : ℂ) + (‖z‖ ^ 2 : ℝ)) f =
      f + fourierMultiplierCLM ℂ (fun z : ℂ => (‖z‖ ^ 2 : ℝ)) f := by
    have h₁ : (fun _ : ℂ => (1 : ℂ)).HasTemperateGrowth := by fun_prop
    have h₂ : (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
    change fourierMultiplierCLM ℂ ((fun _ : ℂ => (1 : ℂ)) +
      (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ))) f = _
    simp only [fourierMultiplierCLM_apply, smulLeftCLM_add h₁ h₂,
      add_apply]
    simp [← fourierMultiplierCLM_apply]
  have hp : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  rw [besselPotential]
  simp only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, Complex.ofReal_add,
    Complex.ofReal_one]
  rw [hadd, laplacian_eq_fourierMultiplierCLM, smul_smul]
  rw [mul_neg, inv_mul_cancel₀ hp, neg_smul, one_smul, sub_neg_eq_add]

theorem memSobolev_two_of_normalized_laplacian
    (f : 𝓢'(ℂ, ℂ)) (g : Lp ℂ 2 (volume : Measure ℂ))
    (h : f - ((2 * Real.pi) ^ 2)⁻¹ • Δ f = (g : 𝓢'(ℂ, ℂ))) :
    MemSobolev 2 2 f := by
  exact ⟨g, (besselPotential_two_eq f).trans h⟩

end KsIndex.Weq
