module

public import KsIndexLean.AlphaRemarkTrial
public import KsIndexLean.PowerArcSamples
public import KsIndexLean.AlphaSeedIntervals

@[expose] public section

/-! Nonvanishing and head normalization of the rational numerical trial. -/

namespace KsIndex.AlphaRemarkTrial
open PowerArc CircleQ Statements
theorem trial_head_re_lower : (9/10 : ℝ) < (trial 0).re := by
  have hg0 := (g_pos_of_mem_unit (β := (5676382/10000000 : ℝ)) (ξ := 0)
    (by norm_num) (by norm_num) (by norm_num)).ne'
  have hb := beta_seed_ratio_bounds
  have hp : 0 < g (5676382/10000000 : ℝ) 1 / g (5676382/10000000 : ℝ) 0 :=
    div_pos (g_pos_of_mem_unit (by norm_num) (by norm_num) (by norm_num))
      (g_pos_of_mem_unit (by norm_num) (by norm_num) (by norm_num))
  have he (n : ℕ) := normalized_g_nat (by norm_num : (0 : ℝ) < 5676382/10000000) n
  simp only [trial, powerTrial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    normalizedPowerField_apply]
  norm_num [Fin.sum_univ_succ, exponent, shift, coefficient, g_neg]
  norm_num at hg0 hp he
  have hratio : (73/100 : ℝ) < g (2838191/5000000 : ℝ) 1 / g (2838191/5000000 : ℝ) 0 := by
    nlinarith [hb.1]
  have h2 := he 2
  have h3 := he 3
  have h4 := he 4
  have h5 := he 5
  have h6 := he 6
  norm_num [normalizedCoefficient, hg0] at h2 h3 h4 h5 h6
  rw [h2, h3, h4, h5, h6, div_self hg0]
  nlinarith


theorem trial_head_ne_zero : trial 0 ≠ 0 := by
  intro h
  have hh := trial_head_re_lower
  rw [h] at hh
  norm_num at hh

noncomputable def headTrial : ℤ → ℂ := (trial 0)⁻¹ • trial

theorem headTrial_memDom : MemDom headTrial := memDom_smul _ trial_memDom

@[simp] theorem headTrial_zero : headTrial 0 = 1 := by
  simp [headTrial, trial_head_ne_zero]

end KsIndex.AlphaRemarkTrial
