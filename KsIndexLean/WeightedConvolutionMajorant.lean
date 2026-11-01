module

public import Mathlib

@[expose] public section


/-! Polynomial majorants for an absolutely convergent transpose convolution. -/
noncomputable section
namespace KsIndex.WeightedConvolution

def weight (n : ℤ) : ℝ := 1 + |(n : ℝ)|

lemma weight_pos (n : ℤ) : 0 < weight n := by unfold weight; positivity

lemma weight_mul (m n : ℤ) : weight n ≤ weight m * weight (m-n) := by
  have h := abs_add_le (m : ℝ) (-((m : ℝ)-n))
  have he : (m : ℝ) + -((m : ℝ)-n) = n := by ring
  rw [he, abs_neg] at h
  unfold weight
  push_cast
  nlinarith [mul_nonneg (abs_nonneg (m : ℝ)) (abs_nonneg ((m : ℝ)-n))]

lemma summable_weight_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℤ => weight n ^ (-p)) := by
  have h : Summable (fun n : ℕ => ((n : ℝ)+1)^(-p)) := by
    have hh := (Real.summable_nat_rpow.mpr (by linarith : -p < -1))
    have hshift := (summable_nat_add_iff 1).mpr hh
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  apply Summable.of_nat_of_neg
  · simpa only [weight, Int.cast_natCast, (fun n : ℕ => abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)), add_comm] using h
  · simpa only [weight, Int.cast_neg, Int.cast_natCast, abs_neg,
      (fun n : ℕ => abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n)), add_comm] using h

/-- A summable separated majorant, with a small decay factor in the output index. -/
lemma kernel_majorant {A B N : ℝ} (hA : 0 < A) (hB : 0 < B) (hN : 0 < N)
    (h : N ≤ A*B) :
    A^(-(3/8 : ℝ)) * B^(-1 : ℝ) ≤
      N^(-(1/16 : ℝ)) * ((1/4 : ℝ)*A^(-(5/4 : ℝ)) +
        (3/4 : ℝ)*B^(-(5/4 : ℝ))) := by
  have hy := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := (1/4 : ℝ)) (w₂ := (3/4 : ℝ))
    (p₁ := A^(-(5/4 : ℝ))) (p₂ := B^(-(5/4 : ℝ)))
    (by norm_num) (by norm_num) (by positivity) (by positivity) (by norm_num)
  rw [← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le] at hy
  norm_num at hy
  have hn := Real.rpow_le_rpow hN.le h (by norm_num : (0 : ℝ) ≤ 1/16)
  rw [Real.mul_rpow hA.le hB.le] at hn
  have hh := mul_le_mul_of_nonneg_left hn
    (by positivity : 0 ≤ A^(-(3/8 : ℝ)) * B^(-1 : ℝ))
  have he : A^(-(3/8 : ℝ)) * B^(-1 : ℝ) *
      (A^(1/16 : ℝ)*B^(1/16 : ℝ)) = A^(-(5/16 : ℝ))*B^(-(15/16 : ℝ)) := by
    calc
      _ = (A^(-(3/8 : ℝ))*A^(1/16 : ℝ)) * (B^(-1 : ℝ)*B^(1/16 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hA, ← Real.rpow_add hB]; norm_num
  rw [he] at hh
  have hb := hh.trans hy
  have hnpos : 0 < N^(1/16 : ℝ) := Real.rpow_pos_of_pos hN _
  have ht := (le_div_iff₀ hnpos).mpr hb
  simpa only [div_eq_mul_inv, ← Real.rpow_neg hN.le, mul_comm] using ht

/-- Absolute convolution with a reciprocal kernel has a decaying row bound. -/
theorem row_summable_and_bound (n : ℤ) :
    Summable (fun m : ℤ => weight m ^ (-(3/8 : ℝ)) * weight (m-n)^(-1 : ℝ)) ∧
    (∑' m : ℤ, weight m ^ (-(3/8 : ℝ)) * weight (m-n)^(-1 : ℝ)) ≤
      weight n ^ (-(1/16 : ℝ)) * (∑' m : ℤ, weight m ^ (-(5/4 : ℝ))) := by
  have hbase := summable_weight_rpow (by norm_num : (1 : ℝ) < 5/4)
  have hshift : Summable (fun m : ℤ => weight (m-n)^(-(5/4 : ℝ))) :=
    hbase.comp_injective (fun a b h => by omega)
  have hsum := ((hbase.mul_left (1/4 : ℝ)).add (hshift.mul_left (3/4 : ℝ))).mul_left
    (weight n ^ (-(1/16 : ℝ)))
  have hb (m : ℤ) := kernel_majorant (weight_pos m) (weight_pos (m-n))
    (weight_pos n) (weight_mul m n)
  have hs : Summable (fun m : ℤ => weight m ^ (-(3/8 : ℝ)) * weight (m-n)^(-1 : ℝ)) :=
    hsum.of_nonneg_of_le (fun m => mul_nonneg (Real.rpow_nonneg (weight_pos m).le _)
      (Real.rpow_nonneg (weight_pos (m-n)).le _)) hb
  refine ⟨hs, ?_⟩
  have hh := hs.tsum_le_tsum hb hsum
  rw [tsum_mul_left, (hbase.mul_left (1/4 : ℝ)).tsum_add (hshift.mul_left (3/4 : ℝ)),
    tsum_mul_left, tsum_mul_left] at hh
  have he := (Equiv.subRight n).tsum_eq (fun m : ℤ => weight m ^ (-(5/4 : ℝ)))
  simp only [Equiv.subRight_apply] at he
  rw [he] at hh
  convert hh using 1 <;> first | rfl | ring

/-- A small decaying weight pairs absolutely with the weighted square domain. -/
theorem summable_pair {z : ℤ → ℝ}
    (hz : Summable (fun n : ℤ => weight n * z n ^ 2)) :
    Summable (fun n : ℤ => weight n ^ (-(1/16 : ℝ)) * |z n|) := by
  have ht := summable_weight_rpow (by norm_num : (1 : ℝ) < 9/8)
  apply ((hz.add ht).mul_left (1/2 : ℝ)).of_nonneg_of_le
  · intro n
    exact mul_nonneg (Real.rpow_nonneg (weight_pos n).le _) (abs_nonneg _)
  · intro n
    have hp := weight_pos n
    have h1 : (weight n ^ (1/2 : ℝ)) ^ 2 = weight n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num
    have h2 : (weight n ^ (-(9/16 : ℝ))) ^ 2 = weight n ^ (-(9/8 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
      norm_num
    have h3 : weight n ^ (1/2 : ℝ) * weight n ^ (-(9/16 : ℝ)) =
        weight n ^ (-(1/16 : ℝ)) := by
      rw [← Real.rpow_add hp]
      norm_num
    have h := sq_nonneg (weight n ^ (1/2 : ℝ) * |z n| - weight n ^ (-(9/16 : ℝ)))
    rw [sub_sq, mul_pow, h1, h2, sq_abs] at h
    have h4 := congrArg (fun x : ℝ => x * |z n|) h3
    nlinarith only [h, h4]

/-- Absolute double summability of the polynomial convolution majorant. -/
theorem summable_double {z : ℤ → ℝ}
    (hz : Summable (fun n : ℤ => weight n * z n ^ 2)) :
    Summable (fun p : ℤ × ℤ =>
      weight p.1 ^ (-(3/8 : ℝ)) * weight (p.1-p.2)^(-1 : ℝ) * |z p.2|) := by
  have hrow (n : ℤ) := (row_summable_and_bound n).1.mul_right |z n|
  have hbound := (summable_pair hz).mul_left
    (∑' m : ℤ, weight m ^ (-(5/4 : ℝ)))
  have hrows : Summable (fun n : ℤ => ∑' m : ℤ,
      weight m ^ (-(3/8 : ℝ)) * weight (m-n)^(-1 : ℝ) * |z n|) := by
    apply hbound.of_nonneg_of_le
    · intro n
      exact tsum_nonneg (fun m => mul_nonneg
        (mul_nonneg (Real.rpow_nonneg (weight_pos m).le _)
          (Real.rpow_nonneg (weight_pos (m-n)).le _)) (abs_nonneg _))
    · intro n
      rw [tsum_mul_right]
      have h := mul_le_mul_of_nonneg_right (row_summable_and_bound n).2 (abs_nonneg (z n))
      convert h using 1 <;> first | rfl | ring
  have hprod : Summable (fun p : ℤ × ℤ =>
      weight p.2 ^ (-(3/8 : ℝ)) * weight (p.2-p.1)^(-1 : ℝ) * |z p.1|) := by
    refine (summable_prod_of_nonneg (f := fun p : ℤ × ℤ =>
      weight p.2 ^ (-(3/8 : ℝ)) * weight (p.2-p.1)^(-1 : ℝ) * |z p.1|) ?_).2 ⟨hrow, hrows⟩
    intro p
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (weight_pos p.2).le _)
      (Real.rpow_nonneg (weight_pos (p.2-p.1)).le _)) (abs_nonneg _)
  exact hprod.prod_symm

/-- Polynomial decay of the first factor suffices for absolute transpose summability. -/
theorem summable_complex_double {a b z : ℤ → ℂ} {C D : ℝ}
    (hC : 0 ≤ C)
    (ha : ∀ m, ‖a m‖ ≤ C * weight m ^ (-(3/8 : ℝ)))
    (hb : ∀ k, ‖b k‖ ≤ D * weight k ^ (-1 : ℝ))
    (hz : Summable (fun n : ℤ => weight n * ‖z n‖ ^ 2)) :
    Summable (fun p : ℤ × ℤ => a p.1 * b (p.1-p.2) * z p.2) := by
  have hm := (summable_double hz).mul_left (C*D)
  have hnorm : Summable (fun p : ℤ × ℤ => ‖a p.1 * b (p.1-p.2) * z p.2‖) := by
    apply hm.of_nonneg_of_le (fun p => norm_nonneg _)
    intro p
    rw [norm_mul, norm_mul, abs_of_nonneg (norm_nonneg _)]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul (ha p.1) (hb (p.1-p.2)) (norm_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (weight_pos p.1).le _))) (norm_nonneg (z p.2))
    convert h using 1 <;> first | rfl | ring
  exact hnorm.of_norm

end KsIndex.WeightedConvolution
