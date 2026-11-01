module

public import KsIndexLean.AlphaFourModePositivity

@[expose] public section


/-! A supplemental certified lower bound for the critical phase. -/
noncomputable section
namespace KsIndex.AlphaFourMode
open Real

lemma tan_pi_fifth_lt : tan (π/5) < (8/11:ℝ) := by
  have hsqrt : (559/250:ℝ) < sqrt 5 := by
    have h := sq_sqrt (show (0:ℝ) ≤ 5 by positivity)
    have hp := sqrt_nonneg (5:ℝ)
    nlinarith
  have hc : (809/1000:ℝ) < cos (π/5) := by rw [cos_pi_div_five]; linarith
  have hcpos : 0 < cos (π/5) := by linarith
  rw [tan_eq_sin_div_cos, div_lt_iff₀ hcpos]
  have hsq := sin_sq_add_cos_sq (π/5)
  have hbound : (121:ℝ) < 185*(cos (π/5))^2 := by nlinarith
  by_contra! h
  nlinarith [sq_nonneg (sin (π/5) - (8/11)*cos (π/5))]

lemma two_fifths_lt_arc_bound : (2/5:ℝ) < 2/π * arctan (8/11) := by
  have h := arctan_strictMono tan_pi_fifth_lt
  rw [arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])] at h
  have hm := mul_lt_mul_of_pos_left h (show 0 < 2/π by positivity)
  have he : 2/π*(π/5) = (2/5:ℝ) := by field_simp
  rwa [he] at hm

theorem arc_bound_lt_alphaStar : 2/π * arctan (8/11) < Staircase.alphaStar := by
  have hs := Staircase.sstar_lt_of_gam_pos (show (0:ℝ)<11/8 by positivity)
    gam_eleven_eighths_pos
  have hi : (8/11:ℝ) < 1/Staircase.sstar := by
    have h := (one_div_lt_one_div (show (0:ℝ)<11/8 by positivity) Staircase.sstar_pos).mpr hs
    norm_num at h ⊢
    exact h
  exact mul_lt_mul_of_pos_left (arctan_strictMono hi) (by positivity)

/-- This strengthens, and does not replace, the paper's original lower bound. -/
theorem two_fifths_lt_alphaStar : (2/5:ℝ) < Staircase.alphaStar :=
  two_fifths_lt_arc_bound.trans arc_bound_lt_alphaStar

end KsIndex.AlphaFourMode
