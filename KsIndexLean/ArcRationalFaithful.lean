module

/-
The rational comparison in the paper's Q-lower proof: R-H >= -7/6 and R >= 4/3.
This retains the two separate inequalities instead of the alternative cubic bound.
-/
public import KsIndexLean.ArcEstimate

@[expose] public section


noncomputable section

namespace KsIndex.ArcRationalFaithful

open KsIndex.ArcEstimate

lemma R_sub_H_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    Rfun a - Hfun a = (-4 * (a * (1 - a)) - 14) /
      ((a * (1 - a)) ^ 2 + 8 * (a * (1 - a)) + 12) := by
  rw [Rfun_eq ha, Hfun_eq ha]
  have hs : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have h2 : 0 < a * (1 - a) + 2 := by positivity
  have h6 : 0 < a * (1 - a) + 6 := by positivity
  have hd : 0 < (a * (1 - a)) ^ 2 + 8 * (a * (1 - a)) + 12 := by positivity
  generalize a * (1 - a) = s at *
  field_simp [ne_of_gt hs, ne_of_gt h2, ne_of_gt h6, ne_of_gt hd]
  ring

lemma R_sub_H_ge (ha : a ∈ Set.Ioo (0 : ℝ) 1) : -7 / 6 ≤ Rfun a - Hfun a := by
  rw [R_sub_H_eq ha]
  have hs : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have hd : 0 < (a * (1 - a)) ^ 2 + 8 * (a * (1 - a)) + 12 := by positivity
  rw [le_div_iff₀ hd]
  nlinarith [sq_nonneg (a * (1 - a))]

lemma R_ge_four_thirds (ha : a ∈ Set.Ioo (0 : ℝ) 1) : 4 / 3 ≤ Rfun a := by
  rw [Rfun_eq ha]
  set s := a * (1 - a)
  have hs : 0 < s := mul_pos ha.1 (by linarith [ha.2])
  have hs' : s ≤ 1 / 4 := by dsimp [s]; nlinarith [sq_nonneg (2 * a - 1)]
  rw [le_div_iff₀ (by positivity : 0 < s * (s + 2))]
  nlinarith [mul_nonneg (show 0 ≤ 1 - 4 * s by linarith) (show 0 ≤ s + 3 by positivity)]

lemma seventy_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) : 70 ≤ 75 * Rfun a - 12 * Hfun a := by
  linarith [R_sub_H_ge ha, R_ge_four_thirds ha]

/-- The exact rational finish displayed in the paper's Q-lower proof. -/
theorem H_bound_lt_R (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    4 * Hfun a / 25 + 32 / 75 < Rfun a := by
  linarith [seventy_le ha]

end KsIndex.ArcRationalFaithful
