module

public import KsIndexLean.PowerArcPolynomialDecay
public import KsIndexLean.WeightedConvolutionMajorant

@[expose] public section


/-! Uniform polynomial decay on shifted integer lattices. -/
noncomputable section
namespace KsIndex.PowerArc
open WeightedConvolution

theorem exists_int_weight_bound {β : ℝ} (hβ : (2/5 : ℝ) ≤ β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, weight n^(11/8 : ℝ) * |g β n| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_nat_weight_bound hβ hβ1
  refine ⟨C, hC, ?_⟩
  intro n
  have hab : (n.natAbs : ℝ) = |(n : ℝ)| := by
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by simp
      _ = _ := by rw [Int.natCast_natAbs, Int.cast_abs]
  have hg : g β |(n : ℝ)| = g β n := by
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · rw [abs_of_nonneg hn]
    · rw [abs_of_neg hn, g_neg]
  have h := hb n.natAbs
  rw [hab, hg] at h
  exact h

lemma weight_le_shifted (m j : ℤ) : weight m ≤ weight (2*m+j) * weight j := by
  have h1 : weight m ≤ weight (2*m) := by
    unfold weight
    push_cast
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg (m : ℝ)]
  have h2 := weight_mul (2*m+j) (2*m)
  rw [show (2*m+j)-(2*m) = j by ring] at h2
  exact h1.trans h2

/-- Every fixed shifted lattice inherits the same decay exponent. -/
theorem exists_shift_decay {β : ℝ} (hβ : (2/5 : ℝ) ≤ β) (hβ1 : β ≤ 1) (j : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℤ,
      |g β (2*(m:ℝ)+j)| ≤ C * weight m ^ (-(11/8 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := exists_int_weight_bound hβ hβ1
  refine ⟨weight j^(11/8 : ℝ)*C,
    mul_nonneg (Real.rpow_nonneg (weight_pos j).le _) hC, ?_⟩
  intro m
  have hp := Real.rpow_le_rpow (weight_pos m).le (weight_le_shifted m j)
    (by norm_num : (0 : ℝ) ≤ 11/8)
  rw [Real.mul_rpow (weight_pos (2*m+j)).le (weight_pos j).le] at hp
  have hg := hb (2*m+j)
  push_cast at hg
  have h : weight m^(11/8 : ℝ) * |g β (2*(m:ℝ)+j)| ≤ weight j^(11/8 : ℝ)*C := by
    calc
      _ ≤ (weight (2*m+j)^(11/8 : ℝ)*weight j^(11/8 : ℝ))*|g β (2*(m:ℝ)+j)| :=
        mul_le_mul_of_nonneg_right hp (abs_nonneg _)
      _ = weight j^(11/8 : ℝ)*(weight (2*m+j)^(11/8 : ℝ)*|g β (2*(m:ℝ)+j)|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (weight_pos j).le _)
  have hd : 0 < weight m^(11/8 : ℝ) := Real.rpow_pos_of_pos (weight_pos m) _
  have hh := (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, ← Real.rpow_neg (weight_pos m).le, mul_comm] using hh

end KsIndex.PowerArc
