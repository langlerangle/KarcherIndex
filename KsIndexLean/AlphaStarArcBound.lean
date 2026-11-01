module

public import KsIndexLean.AlphaStarCertification
public import KsIndexLean.GammaOne

@[expose] public section


/-! An explicit negative spectral certificate from the admissible arc field.
The infinite weighted energy is controlled by its proved exact sum. -/
noncomputable section
namespace KsIndex.AlphaStarBounds
open CircleQ TestField SingleArc GammaOne Real

/-- The normalized coefficient model's unnormalized witness has a fixed negative margin. -/
lemma Qform_one_arcW_le : Qform 1 arcW ≤ -(1 / 32 : ℝ) := by
  rw [Qform_one_arcW]
  linarith [NformArc_third_le]

/-- Uniform bound on the coefficient of s² in the trial energy. -/
lemma arc_minus_energy_le : (∑' m : ℤ, sigM m * ‖convS arcW m‖ ^ 2) ≤ 3 / 4 := by
  have hfull : Summable (fun l : ℤ => 3 * (|(l : ℝ) + 1 / 3| * c l ^ 2)) :=
    (summable_abs_mul_sq (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 3
  have hsub := tsum_comp_le_tsum_of_inj hfull
    (fun l => by positivity) two_mul_add_one_injective
  have hpoint : ∀ m : ℤ, sigM m * ‖convS arcW m‖ ^ 2 ≤
      3 * (|((2*m+1 : ℤ) : ℝ) + 1 / 3| * c (2*m+1) ^ 2) := by
    intro m
    rw [convS_arcW, norm_ofReal_sq]
    have hs : sigM m ≤ |6 * (m : ℝ) + 4| :=
      le_trans (le_abs_self _) (abs_sigM_le m)
    have hw : 3 * |((2*m+1 : ℤ) : ℝ) + 1 / 3| = |6 * (m : ℝ) + 4| := by
      rw [← abs_of_pos (by norm_num : (0 : ℝ) < 3), ← abs_mul]
      congr 1
      push_cast
      ring
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (c (2*m+1)))]
  have hle := (summable_sigM_mul memDom_arcW.2).tsum_le_tsum hpoint
    (hfull.comp_injective two_mul_add_one_injective)
  have htotal : (∑' l : ℤ, 3 * (|(l : ℝ) + 1 / 3| * c l ^ 2)) = 3 / 4 := by
    rw [tsum_mul_left, test_field (show (1 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)]
    norm_num
  exact le_trans hle (by simpa only [htotal, Function.comp_def] using hsub)

/-- A negative least eigenvalue at parameter 51/50. -/
theorem gam_51_50_neg : gam (51 / 50) < 0 := by
  have hdiff : Qform (51 / 50) arcW = Qform 1 arcW +
      ((51 / 50 : ℝ)^2 - 1) * (∑' m : ℤ, sigM m * ‖convS arcW m‖ ^ 2) := by
    simp only [Qform]
    ring
  have hneg : Qform (51 / 50) arcW < 0 := by
    rw [hdiff]
    nlinarith [Qform_one_arcW_le, arc_minus_energy_le]
  exact lt_of_le_of_lt (gam_le_div memDom_arcW normSq_arcW_pos)
    (div_neg_of_neg_of_pos hneg normSq_arcW_pos)

theorem sstar_gt_51_50 : (51 / 50 : ℝ) < Staircase.sstar :=
  Staircase.lt_sstar_of_gam_neg (by norm_num) gam_51_50_neg

/-- An upper bound on the critical phase from the arc-field certificate. -/
theorem alphaStar_lt_arc_bound :
    Staircase.alphaStar < 2 / π * arctan (50 / 51) := by
  have hi : 1 / Staircase.sstar < (50 / 51 : ℝ) := by
    have := (one_div_lt_one_div Staircase.sstar_pos
      (show (0 : ℝ) < 51 / 50 by norm_num)).mpr sstar_gt_51_50
    norm_num at this ⊢
    exact this
  exact mul_lt_mul_of_pos_left (arctan_strictMono hi) (by positivity)

/-- The arc-field upper endpoint is strictly smaller than 1/2. -/
theorem arc_bound_lt_half : 2 / π * arctan (50 / 51) < (1 / 2 : ℝ) := by
  have ha := arctan_strictMono (show (50 / 51 : ℝ) < 1 by norm_num)
  rw [arctan_one] at ha
  have hb := mul_lt_mul_of_pos_left ha (show (0 : ℝ) < 2 / π by positivity)
  have he : 2 / π * (π / 4) = (1 / 2 : ℝ) := by field_simp; ring
  rwa [he] at hb

end KsIndex.AlphaStarBounds
