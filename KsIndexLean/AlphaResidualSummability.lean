module

public import KsIndexLean.AlphaResidualRepresentation
public import KsIndexLean.WeightedConvolutionMajorant

@[expose] public section


/-! Sufficient polynomial decay for the actual circle-form transpose series. -/
noncomputable section
namespace KsIndex.AlphaResidual
open CircleQ WeightedConvolution

lemma weight_le_freqP (n : ℤ) : weight n ≤ |6 * (n : ℝ) + 1| := by
  unfold weight
  rcases le_or_gt 0 n with hn | hn
  · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg hn', abs_of_nonneg (by linarith : (0 : ℝ) ≤ 6*(n:ℝ)+1)]
    linarith
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith : (n : ℝ) ≤ 0),
      abs_of_nonpos (by linarith : 6*(n:ℝ)+1 ≤ 0)]
    linarith

lemma memDom_weight_summable {z : ℤ → ℂ} (hz : MemDom z) :
    Summable (fun n : ℤ => weight n * ‖z n‖^2) := by
  apply hz.1.of_nonneg_of_le
  · intro n
    exact mul_nonneg (weight_pos n).le (sq_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_right (weight_le_freqP n) (sq_nonneg _)

lemma weight_le_twice_odd (n : ℤ) : weight n ≤ 2 * |2*(n:ℝ)+1| := by
  unfold weight
  rcases le_or_gt 0 n with hn | hn
  · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_of_nonneg hn', abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2*(n:ℝ)+1)]
    linarith
  · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith : (n : ℝ) ≤ 0),
      abs_of_nonpos (by linarith : 2*(n:ℝ)+1 ≤ 0)]
    linarith

lemma chat_decay (n : ℤ) : ‖(chat n : ℂ)‖ ≤ 4 * weight n ^ (-1 : ℝ) := by
  have hw := weight_pos n
  have ho : 0 < |2*(n:ℝ)+1| := by linarith [weight_le_twice_odd n]
  have hpi : 0 ≤ (2 : ℝ)/Real.pi := by positivity
  have hpi2 : (2 : ℝ)/Real.pi ≤ 2 := by
    apply (div_le_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  rw [Complex.norm_real, Real.norm_eq_abs, chat, abs_div, abs_mul,
    abs_of_nonneg hpi, abs_zpow, abs_neg, abs_one, one_zpow, mul_one,
    Real.rpow_neg_one, ← div_eq_mul_inv]
  apply (div_le_iff₀ ho).2
  apply hpi2.trans
  rw [div_mul_eq_mul_div, le_div_iff₀ hw]
  nlinarith [weight_le_twice_odd n]

/-- The only remaining analytic input is decay of the first transpose factor. -/
theorem double_summable_of_decay {w z : ℤ → ℂ} {C : ℝ}
    (hC : 0 ≤ C)
    (hw : ∀ m, ‖(sigM m : ℂ) * (starRingEnd ℂ) (convS w m)‖ ≤
      C * weight m ^ (-(3/8 : ℝ))) (hz : MemDom z) :
    Summable (fun p : ℤ × ℤ => (sigM p.1 : ℂ) *
      (starRingEnd ℂ) (convS w p.1) * (chat (p.1-p.2) : ℂ) * z p.2) :=
  summable_complex_double
    (a := fun m => (sigM m : ℂ) * (starRingEnd ℂ) (convS w m))
    (b := fun k => (chat k : ℂ)) (z := z)
    hC hw chat_decay (memDom_weight_summable hz)

lemma sigM_weight_bound (m : ℤ) : |sigM m| ≤ 6 * weight m := by
  apply (abs_sigM_le m).trans
  have h := abs_add_le (6*(m:ℝ)) 4
  rw [abs_mul] at h
  norm_num at h
  unfold weight
  linarith

/-- A power-arc decay bound gives the symbol-weighted transpose decay. -/
lemma transpose_factor_decay {w : ℤ → ℂ} {C : ℝ}
    (hw : ∀ m, ‖convS w m‖ ≤ C * weight m ^ (-(11/8 : ℝ))) (m : ℤ) :
    ‖(sigM m : ℂ) * (starRingEnd ℂ) (convS w m)‖ ≤
      (6*C) * weight m ^ (-(3/8 : ℝ)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  have h := mul_le_mul (sigM_weight_bound m) (hw m) (norm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (weight_pos m).le)
  have he : weight m * weight m ^ (-(11/8 : ℝ)) = weight m ^ (-(3/8 : ℝ)) := by
    nth_rw 1 [← Real.rpow_one (weight m)]
    rw [← Real.rpow_add (weight_pos m)]
    norm_num
  calc
    _ ≤ (6 * weight m) * (C * weight m ^ (-(11/8 : ℝ))) := h
    _ = (6*C) * (weight m * weight m ^ (-(11/8 : ℝ))) := by ring
    _ = _ := by rw [he]

end KsIndex.AlphaResidual
