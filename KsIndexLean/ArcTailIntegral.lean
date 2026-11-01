module

/-
The cubic sum in the paper's Q-lower estimate. The strict inequality is obtained
from the strict gap on [1,2] in the decreasing-function integral comparison.
-/
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic

@[expose] public section


noncomputable section

namespace KsIndex.ArcTailIntegral

open MeasureTheory Set

/-- The decreasing integrand used in the paper's tail estimate. -/
def cube (x : ℝ) : ℝ := 1 / x ^ 3

lemma cube_eq_rpow (x : ℝ) : cube x = x ^ (-3 : ℝ) := by
  simp [cube, zpow_neg, zpow_ofNat, one_div]

lemma integrable_cube {c : ℝ} (hc : 0 < c) : IntegrableOn cube (Ioi c) := by
  rw [show cube = (fun x : ℝ => x ^ (-3 : ℝ)) from funext cube_eq_rpow]
  exact integrableOn_Ioi_rpow_of_lt (by norm_num) hc

lemma integral_cube {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi c, cube x = 1 / (2 * c ^ 2) := by
  simp_rw [cube_eq_rpow]
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hc]
  norm_num [Real.rpow_neg_natCast, zpow_neg, zpow_ofNat]
  ring

lemma antitone_cube {c : ℝ} (hc : 0 < c) : AntitoneOn cube (Ici c) := by
  intro x hx y hy hxy
  exact one_div_le_one_div_of_le (pow_pos (lt_of_lt_of_le hc hx) 3)
    (pow_le_pow_left₀ (le_of_lt (lt_of_lt_of_le hc hx)) hxy 3)

lemma summable_cube_nat : Summable fun n : ℕ => cube n := by
  apply AntitoneOn.summable_of_integrableOn_Ioi (N := 1)
  · simpa only [Nat.cast_one] using antitone_cube (by norm_num : (0 : ℝ) < 1)
  · simpa only [Nat.cast_one] using integrable_cube (by norm_num : (0 : ℝ) < 1)
  · intro x hx
    have : 0 < x := lt_trans (by norm_num) hx
    unfold cube
    positivity

lemma summable_cube_shift (k : ℕ) : Summable fun n : ℕ => cube (n + k) := by
  simpa only [Nat.cast_add] using (summable_nat_add_iff k).mpr summable_cube_nat

/-- The strict rectangle/integral gap in the first unit interval. -/
lemma first_interval_gap : cube 2 < ∫ x in (1 : ℝ)..2, cube x := by
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (integrable_cube (by norm_num : (0 : ℝ) < 1)) (by norm_num : (1 : ℝ) ≤ 2)
  rw [integral_cube (by norm_num), integral_cube (by norm_num)] at h
  rw [← h]
  norm_num [cube]

/-- The paper's strict integral test, with the gap on [1,2] displayed explicitly. -/
theorem cube_sum_lt_integral :
    (∑' n : ℕ, cube ((n : ℝ) + 2)) < ∫ x in Ioi (1 : ℝ), cube x := by
  have hrest := (antitone_cube (by norm_num : (0 : ℝ) < 2)).tsum_comp_add_le_integral 2
    (integrable_cube (by norm_num : (0 : ℝ) < 2))
    (fun x hx => show 0 ≤ cube x by
      have : 0 < x := lt_trans (by norm_num) hx
      unfold cube
      positivity)
  have hsplit := (summable_cube_shift 2).tsum_eq_zero_add
  have hdecomp := intervalIntegral.integral_Ioi_sub_Ioi
    (integrable_cube (by norm_num : (0 : ℝ) < 1)) (by norm_num : (1 : ℝ) ≤ 2)
  have hgap := first_interval_gap
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hrest
  simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hsplit
  have heq : (∑' n : ℕ, cube ((n : ℝ) + 1 + 2)) =
      ∑' n : ℕ, cube ((n : ℝ) + 2 + 1) := by congr 1; funext n; congr 1; ring
  rw [heq] at hsplit
  linarith

/-- The strict numerical bound retains the paper's improper integral as an intermediate. -/
theorem cube_sum_lt_half : (∑' n : ℕ, cube ((n : ℝ) + 2)) < 1 / 2 := by
  have := cube_sum_lt_integral
  rwa [integral_cube (by norm_num : (0 : ℝ) < 1), one_pow, mul_one] at this

open Classical in
/-- The four modes excluded from the cubic tail. -/
def cubeTerm (l : ℤ) : ℝ :=
  if l = -2 ∨ l = -1 ∨ l = 0 ∨ l = 1 then 0 else cube (|(l : ℝ)| - 1)

lemma cubeTerm_nat_shift (n : ℕ) : cubeTerm (n + 2) = cube ((n : ℝ) + 1) := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  simp only [cubeTerm]
  rw [if_neg (by omega)]
  push_cast
  rw [abs_of_nonneg (by positivity)]
  congr 1
  ring

lemma cubeTerm_neg_shift (n : ℕ) : cubeTerm (-(n + 3)) = cube ((n : ℝ) + 2) := by
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  simp only [cubeTerm]
  rw [if_neg (by omega)]
  push_cast
  rw [abs_of_nonpos (by linarith)]
  congr 1
  ring

lemma summable_cubeTerm_pos : Summable fun n : ℕ => cubeTerm n := by
  apply (summable_nat_add_iff 2).mp
  simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, cubeTerm_nat_shift] using
    summable_cube_shift 1

lemma summable_cubeTerm_neg : Summable fun n : ℕ => cubeTerm (-(n + 1)) := by
  apply (summable_nat_add_iff 2).mp
  apply (summable_cube_shift 2).congr
  intro n
  rw [show -((↑(n + 2) : ℤ) + 1) = -((n : ℤ) + 3) by push_cast; ring,
    cubeTerm_neg_shift]
  norm_num

lemma summable_cubeTerm : Summable cubeTerm :=
  summable_cubeTerm_pos.of_nat_of_neg_add_one summable_cubeTerm_neg

/-- l=2 contributes once; every subsequent absolute denominator occurs twice. -/
theorem tsum_cubeTerm :
    ∑' l : ℤ, cubeTerm l = 1 + 2 * ∑' n : ℕ, cube ((n : ℝ) + 2) := by
  rw [tsum_of_nat_of_neg_add_one summable_cubeTerm_pos summable_cubeTerm_neg]
  have hp := summable_cubeTerm_pos.sum_add_tsum_nat_add 2
  have hn := summable_cubeTerm_neg.sum_add_tsum_nat_add 2
  have hs := (summable_cube_shift 1).tsum_eq_zero_add
  have h0 : cubeTerm 0 = 0 := by norm_num [cubeTerm]
  have h1 : cubeTerm 1 = 0 := by norm_num [cubeTerm]
  have hn1 : cubeTerm (-1) = 0 := by norm_num [cubeTerm]
  have hn2 : cubeTerm (-2) = 0 := by norm_num [cubeTerm]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, zero_add, show -(1 + 1 : ℤ) = -2 by norm_num, h0, h1, hn1, hn2] at hp hn
  simp only [Nat.cast_add, Nat.cast_ofNat, cubeTerm_nat_shift] at hp
  have he : (fun n : ℕ => cubeTerm (-(↑(n + 2) + 1))) =
      fun n : ℕ => cube ((n : ℝ) + 2) := by
    funext n
    rw [show -((↑(n + 2) : ℤ) + 1) = -((n : ℤ) + 3) by push_cast; ring,
      cubeTerm_neg_shift]
  rw [he] at hn
  simp only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one] at hs
  rw [show cube 1 = 1 by norm_num [cube]] at hs
  have he' : (∑' n : ℕ, cube ((n : ℝ) + 1 + 1)) =
      ∑' n : ℕ, cube ((n : ℝ) + 2) := by congr 1; funext n; congr 1; ring
  rw [he'] at hs
  linarith

theorem tsum_cubeTerm_lt_two : (∑' l : ℤ, cubeTerm l) < 2 := by
  rw [tsum_cubeTerm]
  linarith [cube_sum_lt_half]

end KsIndex.ArcTailIntegral
