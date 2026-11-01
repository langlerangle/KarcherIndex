module

public import KsIndexLean.AlphaStarArcBound

@[expose] public section


/-! A sharper rational certificate obtained by retaining low Fourier modes. -/
noncomputable section
namespace KsIndex.AlphaStarBounds
open CircleQ TestField SingleArc GammaOne Real

lemma arc_even_weight_lower :
    (251 : ℝ) / 800 < ∑' n : ℤ, |6 * (n : ℝ) + 1| * c (2*n) ^ 2 := by
  have h := summable_even_weight.sum_le_tsum
    ({0,-1,-2,-3,-4} : Finset ℤ) (fun n _ => by positivity)
  have hm2 : c (-2)^2 = 1/32 := by
    rw [show (-2:ℤ) = -1-1 by ring, c_reflect, c_one_sq]
  have hm4 : c (-4)^2 = 1/512 := by
    rw [show (-4:ℤ) = -3-1 by ring, c_reflect]
    have := c_odd_sq 1
    norm_num [catalan] at this
    exact this
  have hm6 : c (-6)^2 = 1/2048 := by
    rw [show (-6:ℤ) = -5-1 by ring, c_reflect]
    have := c_odd_sq 2
    norm_num [catalan] at this
    exact this
  have hm8 : c (-8)^2 = 25/131072 := by
    rw [show (-8:ℤ) = -7-1 by ring, c_reflect]
    have := c_odd_sq 3
    norm_num [catalan_three] at this
    exact this
  norm_num [Finset.sum_insert, c_zero_sq, hm2, hm4, hm6, hm8] at h
  linarith

lemma arc_weight_split :
    (∑' n : ℤ, |6 * (n : ℝ) + 1| * c (2*n)^2) +
    (∑' m : ℤ, |6 * (m : ℝ) + 4| * c (2*m+1)^2) = 3/4 := by
  have hf := (summable_abs_mul_sq
    (show (1/3:ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 3
  have he : (fun n : ℤ => 3 * (|((2*n:ℤ):ℝ)+1/3| * c (2*n)^2)) =
      (fun n : ℤ => |6*(n:ℝ)+1| * c (2*n)^2) := by
    funext n
    rw [← mul_assoc, ← abs_of_pos (show (0:ℝ)<3 by norm_num), ← abs_mul]
    congr 2
    push_cast
    ring
  have ho : (fun m : ℤ => 3 * (|((2*m+1:ℤ):ℝ)+1/3| * c (2*m+1)^2)) =
      (fun m : ℤ => |6*(m:ℝ)+4| * c (2*m+1)^2) := by
    funext m
    rw [← mul_assoc, ← abs_of_pos (show (0:ℝ)<3 by norm_num), ← abs_mul]
    congr 2
    push_cast
    ring
  have hs := tsum_int_even_add_odd hf
  rw [he, ho, tsum_mul_left, test_field (show (1/3:ℝ) ∈ Set.Ioo 0 1 by norm_num)] at hs
  linarith

lemma arc_minus_energy_refined :
    (∑' m : ℤ, sigM m * ‖convS arcW m‖ ^ 2) < 31/200 := by
  let D : ℤ → ℝ := fun m =>
    |6*(m:ℝ)+4| * c (2*m+1)^2 - sigM m * ‖convS arcW m‖^2
  have hd : Summable D := summable_odd_weight.sub (summable_sigM_mul memDom_arcW.2)
  have hn : ∀ m, 0 ≤ D m := by
    intro m
    dsimp [D]
    rw [convS_arcW, norm_ofReal_sq]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_right
      (le_trans (le_abs_self _) (abs_sigM_le m)) (sq_nonneg _))
  have h := hd.sum_le_tsum ({-1,0}:Finset ℤ) (fun m _ => hn m)
  have hm1 : c (-1)^2 = 1/8 := by
    rw [show (-1:ℤ) = -0-1 by ring, c_reflect, c_zero_sq]
  have hv : ∑ m ∈ ({-1,0}:Finset ℤ), D m = 9/32 := by
    norm_num [D, Finset.sum_insert, convS_arcW, norm_ofReal_sq, sigM, hm1, c_one_sq]
  rw [hv] at h
  have ht : (∑' m, D m) =
      (∑' m : ℤ, |6*(m:ℝ)+4| * c (2*m+1)^2) -
      (∑' m : ℤ, sigM m * ‖convS arcW m‖^2) :=
    summable_odd_weight.tsum_sub (summable_sigM_mul memDom_arcW.2)
  rw [ht] at h
  linarith [arc_weight_split, arc_even_weight_lower]

/-- A rational negative certificate with the refined arc-field estimates. -/
theorem gam_7_6_neg : gam (7 / 6) < 0 := by
  have hq : Qform 1 arcW ≤ -(9/160 : ℝ) := by
    rw [Qform_one_arcW]
    linarith [NformArc_third_le_sharp]
  have he : Qform (7/6) arcW = Qform 1 arcW +
      ((7/6:ℝ)^2-1)*(∑' m : ℤ, sigM m * ‖convS arcW m‖^2) := by
    simp only [Qform]
    ring
  have hn : Qform (7/6) arcW < 0 := by
    rw [he]
    nlinarith [arc_minus_energy_refined]
  exact lt_of_le_of_lt (gam_le_div memDom_arcW normSq_arcW_pos)
    (div_neg_of_neg_of_pos hn normSq_arcW_pos)

theorem sstar_gt_7_6 : (7/6:ℝ) < Staircase.sstar :=
  Staircase.lt_sstar_of_gam_neg (by norm_num) gam_7_6_neg

/-- Refined critical-phase upper bound. -/
theorem alphaStar_lt_refined_arc_bound :
    Staircase.alphaStar < 2/π * arctan (6/7) := by
  have hi : 1/Staircase.sstar < (6/7:ℝ) := by
    have := (one_div_lt_one_div Staircase.sstar_pos
      (show (0:ℝ)<7/6 by norm_num)).mpr sstar_gt_7_6
    norm_num at this ⊢
    exact this
  exact mul_lt_mul_of_pos_left (arctan_strictMono hi) (by positivity)

end KsIndex.AlphaStarBounds
