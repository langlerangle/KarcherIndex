module

public import KsIndexLean.AlphaTrialReducedReflected

@[expose] public section


/-! Shifted moments of the nonnegative-frequency trial convolution. -/
noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real PowerArc KsIndex.AlphaRemarkTrial

def positiveDemod (t : ℕ) : ℝ := (-1 : ℝ)^t * vTrial t

lemma summable_abs_positiveDemod : Summable (fun t : ℕ => |positiveDemod t|) := by
  have h := summable_abs_vTrial.comp_injective
    ((fun a b h => by simp only at h; omega) : Function.Injective (fun t : ℕ => (t : ℤ)))
  simpa only [Function.comp_def, positiveDemod, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul] using h

lemma summable_positiveDemod : Summable positiveDemod :=
  Summable.of_abs summable_abs_positiveDemod

lemma summable_positiveDemod_div {z : ℝ} (hz : 0 < z) :
    Summable (fun t : ℕ => positiveDemod t / ((t : ℝ) + z)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun t => abs_nonneg _) (fun t => ?_)
    (summable_abs_positiveDemod.mul_left (1 / z))
  have hab : (0 : ℝ) < (t : ℝ) + z := by positivity
  have h1 : z ≤ (t : ℝ) + z := by
    have := Nat.cast_nonneg (α := ℝ) t
    linarith
  rw [abs_div, abs_of_pos hab,
    show 1 / z * |positiveDemod t| = |positiveDemod t| / z by ring]
  gcongr


lemma positiveDemod_eq_sum (t : ℕ) :
    positiveDemod t = (-1 : ℝ)^t * ∑ i : Fin 25, (coefficient i).re *
      (g (exponent i) ((2*(t : ℝ)+1)+shift i)/g (exponent i) 0) := by
  rw [positiveDemod, vTrial_eq_sum]
  simp only [Int.cast_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show 2*(t : ℝ)+((shift i : ℝ)+1) = (2*(t : ℝ)+1)+shift i by ring]

lemma summable_term_stieltjes_plus (i : Fin 25) {z : ℝ} (hz : 0 < z) :
    Summable (fun k : ℕ =>
      ((-1 : ℝ) ^ k * g (exponent i) ((9 + shift i) + 2 * k)) / ((k : ℝ) + z)) := by
  have hr : exponent i ≤ 9 + (shift i : ℝ) := exponent_le_baseterm_refl i
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((abs_g_summable (exponent_pos i) hr).mul_left (1 / z))
  have hab : (0 : ℝ) < (k : ℝ) + z := by positivity
  have h1 : z ≤ (k : ℝ) + z := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hab,
    show 1 / z * |g (exponent i) ((9 + (shift i : ℝ)) + 2 * k)| =
      |g (exponent i) ((9 + (shift i : ℝ)) + 2 * k)| / z by ring]
  gcongr

/-- For `z > 0`, the nonnegative-frequency demodulated sum against
`1/(t+z)` equals the `t = 0..3` prefix plus the 25-term symbolic Stieltjes
combination at `z + 4`. -/
theorem positive_shifted_tsum (z : ℝ) (hz : 0 < z) :
    (∑' t : ℕ, positiveDemod t / ((t : ℝ) + z)) =
      (∑ t ∈ Finset.range 4, positiveDemod t / ((t : ℝ) + z))
      + ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
          powerArcStieltjes (exponent i) (9 + shift i) (z + 4) := by
  rw [← (summable_positiveDemod_div hz).sum_add_tsum_nat_add 4]
  congr 1
  have hterm : (fun k : ℕ => positiveDemod (k + 4) / (((k + 4 : ℕ) : ℝ) + z)) =
      fun k : ℕ => ∑ i : Fin 25, ((coefficient i).re / g (exponent i) 0) *
        (((-1 : ℝ) ^ k * g (exponent i) ((9 + shift i) + 2 * k)) /
          ((k : ℝ) + (z + 4))) := by
    funext k
    rw [positiveDemod_eq_sum, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [show ((2 * ((k + 4 : ℕ) : ℝ) + 1) + (shift i : ℝ)) =
        (9 + (shift i : ℝ)) + 2 * k by push_cast; ring,
      show (((k + 4 : ℕ) : ℝ) + z) = (k : ℝ) + (z + 4) by push_cast; ring,
      pow_add]
    norm_num
    ring
  rw [hterm, Summable.tsum_finsetSum (fun i _ =>
    (summable_term_stieltjes_plus i (by linarith : (0:ℝ) < z + 4)).mul_left _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, powerArcStieltjes]


end KsIndex.OppositeHalf
