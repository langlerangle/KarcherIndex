module

public import KsIndexLean.AlphaOppositeHalfGroups

@[expose] public section


/-! Upward peeling of the power-arc Stieltjes transform.

For `β > 0`, `r ≥ β` and `z > 0`, the identity
`H(r, z) = g(β,r)/z − H(r+2, z+1)` extracts one term.
Iteration gives a finite prefix and a signed terminal transform at
`(r + 2k, z + k)`. The fixed-base recurrence is treated separately. -/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ Real PowerArc

lemma summable_paS_terms {β r z : ℝ} (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z) :
    Summable (fun k : ℕ => ((-1 : ℝ) ^ k * g β (r + 2 * k)) / ((k : ℝ) + z)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    ((abs_g_summable hβ hr).mul_left (1 / z))
  have hab : (0 : ℝ) < (k : ℝ) + z := by positivity
  have h1 : z ≤ (k : ℝ) + z := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos hab,
    show 1 / z * |g β (r + 2 * k)| = |g β (r + 2 * k)| / z by ring]
  gcongr

/-- Extract the first term of the transform for `β > 0`, `r ≥ β` and `z > 0`. -/
theorem paS_peel {β r z : ℝ} (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z) :
    powerArcStieltjes β r z = g β r / z - powerArcStieltjes β (r + 2) (z + 1) := by
  rw [powerArcStieltjes, (summable_paS_terms hβ hr hz).tsum_eq_zero_add]
  have hre : (fun k : ℕ => ((-1 : ℝ) ^ (k + 1) * g β (r + 2 * ((k : ℕ) + 1 : ℕ))) /
      (((k : ℕ) + 1 : ℕ) + z)) =
      fun k : ℕ => -(((-1 : ℝ) ^ k * g β ((r + 2) + 2 * k)) / ((k : ℝ) + (z + 1))) := by
    funext k
    rw [pow_succ]
    push_cast
    rw [show (r + 2 * ((k : ℝ) + 1)) = (r + 2) + 2 * k by ring,
      show ((k : ℝ) + 1 + z) = (k : ℝ) + (z + 1) by ring]
    ring
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, add_zero, zero_add]
  rw [hre, tsum_neg, powerArcStieltjes]
  ring

/-- Iterated upward peel: an explicit `k`-term prefix plus the signed terminal
transform at `(r + 2k, z + k)`. -/
theorem paS_iter {β r z : ℝ} (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z) (k : ℕ) :
    powerArcStieltjes β r z =
      (∑ u ∈ Finset.range k, (-1 : ℝ) ^ u * g β (r + 2 * u) / (z + u))
      + (-1 : ℝ) ^ k * powerArcStieltjes β (r + 2 * k) (z + k) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [ih, Finset.sum_range_succ]
      have hrm : β ≤ r + 2 * m := by
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      have hzm : (0 : ℝ) < z + m := by
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      rw [paS_peel hβ hrm hzm]
      rw [show (r + 2 * m + 2) = r + 2 * ((m : ℕ) + 1 : ℕ) by push_cast; ring,
        show (z + (m : ℝ) + 1) = z + ((m : ℕ) + 1 : ℕ) by push_cast; ring,
        pow_succ]
      push_cast
      ring

end KsIndex.OppositeHalf
