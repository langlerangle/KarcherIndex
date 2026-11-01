module

public import KsIndexLean.AlphaStarArcRefined

@[expose] public section


/-! A full-domain positive certificate from the weighted Cauchy–Schwarz bound. -/
noncomputable section
namespace KsIndex.AlphaStarBounds
open CircleQ Threshold Real

set_option maxHeartbeats 800000 in
/-- A longer rational partial sum strengthens the weighted-CS margin. -/
lemma threshold_partial_margin : (7/810:ℝ) ≤ ∑' n : ℤ, term n := by
  let S : Finset ℤ := {-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}
  have hs : ∑ n ∈ S, term n ≥ (7/810:ℝ) := by
    norm_num [S, Finset.sum_insert, term_eq, brn]
  have hn : ∀ n ∉ S, 0 ≤ term n := by
    intro n hn
    apply term_nonneg_of_notMem
    intro hi
    have hh : n ∈ S := by
      simp only [Finset.mem_Icc] at hi
      obtain ⟨hlo, hhi⟩ := hi
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      omega
    exact hn hh
  exact le_trans hs (summable_term.sum_le_tsum S hn)

lemma weighted_cs_margin : (7/360:ℝ) ≤ 1 - 9 * ∑' n : ℤ, Aweight n := by
  have hpi : π^2 ≠ 0 := pow_ne_zero 2 pi_ne_zero
  have hAsum : (∑' n : ℤ, Aweight n) = (4/π^2) * ∑' n : ℤ, Aterm n := by
    rw [← tsum_mul_left]
    exact tsum_congr Aweight_eq
  have ht : (∑' n : ℤ, term n) = π^2/36 - ∑' n : ℤ, Aterm n := by
    change (∑' n : ℤ, (1/(6*(n:ℝ)+3)^2 - Aterm n)) = _
    rw [hasSum_int_six_shift_sq_inv.summable.tsum_sub summable_Aterm,
      hasSum_int_six_shift_sq_inv.tsum_eq]
  have he : π^2 * (1-9*∑' n : ℤ, Aweight n) = 36 * ∑' n : ℤ, term n := by
    rw [hAsum, ht]
    field_simp
    ring
  have hp : 0 < 1-9*∑' n : ℤ, Aweight n := by linarith [nine_A_lt_one]
  have hpi16 : π^2 ≤ 16 := by nlinarith [pi_lt_four, pi_pos]
  have hh := mul_le_mul_of_nonneg_right hpi16 hp.le
  nlinarith [threshold_partial_margin]

/-- Uniform lower bound on the entire normalized form domain. -/
lemma qform_sqrt_three_margin {u : ℤ → ℂ} (hu : MemDom u) (hn : normSq u = 1) :
    (7/60:ℝ) ≤ Qform (sqrt 3) u := by
  have hb := Bweight_ge hu
  rw [hn, mul_one] at hb
  have hh := qform_sqrt_three_lb hu
  have hm := weighted_cs_margin
  nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ 1-9*∑' n : ℤ, Aweight n by linarith)]

/-- Positive least eigenvalue at a rational parameter below sqrt(3). -/
theorem gam_17_10_pos : 0 < gam (17/10) := by
  apply Staircase.gam_pos_of_positive_form (by norm_num)
  intro u hu hn
  have hq := qform_sqrt_three_margin hu hn
  have ha := Qtau_ge_neg_three (τ := 0) (by norm_num) hu hn
  have he : Qform (17/10) u = (289/300:ℝ)*Qform (sqrt 3) u + (11/300:ℝ)*Qtau 0 u := by
    simp only [Qform, Qtau, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    ring
  rw [he]
  linarith

theorem sstar_lt_17_10 : Staircase.sstar < (17/10:ℝ) :=
  Staircase.sstar_lt_of_gam_pos (by norm_num) gam_17_10_pos

/-- Certified lower endpoint for the critical phase. -/
theorem positive_bound_lt_alphaStar :
    2/π * arctan (10/17) < Staircase.alphaStar := by
  have hi : (10/17:ℝ) < 1/Staircase.sstar := by
    have := (one_div_lt_one_div (show (0:ℝ)<17/10 by norm_num)
      Staircase.sstar_pos).mpr sstar_lt_17_10
    norm_num at this ⊢
    exact this
  exact mul_lt_mul_of_pos_left (arctan_strictMono hi) (by positivity)

/-- The lower endpoint is strictly greater than 1/3. -/
theorem third_lt_positive_bound : (1/3:ℝ) < 2/π * arctan (10/17) := by
  have hs : (17/10:ℝ) < sqrt 3 := by
    have := sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have := sqrt_nonneg (3:ℝ)
    nlinarith
  have hi : 1/sqrt 3 < (10/17:ℝ) := by
    have := one_div_lt_one_div_of_lt (show (0:ℝ)<17/10 by norm_num) hs
    norm_num at this ⊢
    exact this
  have hv : arctan (1/sqrt 3) = π/6 := by
    have ht : tan (π/6) = 1/sqrt 3 := by
      rw [tan_eq_sin_div_cos, sin_pi_div_six, cos_pi_div_six]
      field_simp
    rw [← ht]
    exact arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])
  have ha := arctan_strictMono hi
  rw [hv] at ha
  have hh := mul_lt_mul_of_pos_left ha (show (0:ℝ)<2/π by positivity)
  have he : 2/π*(π/6) = (1/3:ℝ) := by field_simp; ring
  rwa [he] at hh

/-- A certified two-sided critical-phase interval from positive and negative certificates. -/
theorem alphaStar_refined_interval :
    Staircase.alphaStar ∈ Set.Ioo (2/π*arctan (10/17)) (2/π*arctan (6/7)) :=
  ⟨positive_bound_lt_alphaStar, alphaStar_lt_refined_arc_bound⟩

end KsIndex.AlphaStarBounds
