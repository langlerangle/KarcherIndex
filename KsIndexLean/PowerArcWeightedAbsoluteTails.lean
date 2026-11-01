module

public import KsIndexLean.PowerArcSignedTails

@[expose] public section


/-! Exact weighted absolute tails of power-arc coefficients.

The recurrence supplies telescoping sums with one or two rational denominator
factors. These formulas avoid approximating fractional powers in tail estimates.
-/

namespace KsIndex.PowerArc

theorem abs_g_over_linear_hasSum {β r : ℝ} (hβ : 0 < β) (hr : β ≤ r) :
    HasSum (fun n : ℕ => |g β (r + 2 * n)| / (r + 2 * n + β + 2))
      (|g β r| / (2 * (β + 1))) := by
  let f : ℕ → ℝ := fun n => |g β (r + 2 * n)|
  have hs : Summable f := abs_g_summable hβ hr
  have ht : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).2 hs
  have htel : (∑' n, f n) - (∑' n, f (n + 1)) = f 0 := by
    have hh := hs.tsum_eq_zero_add
    linarith
  have hpos : 0 < 2 * (β + 1) := by positivity
  have heq (n : ℕ) : |g β (r + 2 * n)| / (r + 2 * n + β + 2) =
      (f n - f (n + 1)) / (2 * (β + 1)) := by
    have hn : β ≤ r + 2 * n := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hd : 0 < r + 2 * n + β + 2 := by linarith
    apply (div_eq_div_iff hd.ne' hpos.ne').2
    have hh := abs_g_step hβ hn
    dsimp [f]
    rw [show r + 2 * ((n + 1 : ℕ) : ℝ) = (r + 2 * n) + 2 by push_cast; ring]
    nlinarith
  have hh := (hs.hasSum.sub ht.hasSum).div_const (2 * (β + 1))
  rw [htel] at hh
  simpa only [← heq, f, Nat.cast_zero, mul_zero, add_zero] using hh

/-- The second weighted tail also telescopes, with an explicit endpoint formula. -/
theorem abs_g_over_two_linear_hasSum {β r : ℝ} (hβ : 0 < β) (hr : β ≤ r) :
    HasSum (fun n : ℕ => |g β (r + 2 * n)| /
      ((r + 2 * n + β + 2) * (r + 2 * n + β + 4)))
      (|g β r| / (2 * (β + 2) * (r + β + 2))) := by
  let f : ℕ → ℝ := fun n => |g β (r + 2 * n)| / (r + 2 * n + β + 2)
  have hs : Summable f := (abs_g_over_linear_hasSum hβ hr).summable
  have ht : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).2 hs
  have htel : (∑' n, f n) - (∑' n, f (n + 1)) = f 0 := by
    have hh := hs.tsum_eq_zero_add
    linarith
  have heq (n : ℕ) : |g β (r + 2 * n)| /
      ((r + 2 * n + β + 2) * (r + 2 * n + β + 4)) =
      (f n - f (n + 1)) / (2 * (β + 2)) := by
    have hn : β ≤ r + 2 * n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hd : 0 < r + 2 * n + β + 2 := by linarith
    have he : 0 < r + 2 * n + β + 4 := by linarith
    have hb : 0 < β + 2 := by linarith
    have hh := abs_g_step hβ hn
    dsimp [f]
    rw [show r + 2 * ((n + 1 : ℕ) : ℝ) = (r + 2 * n) + 2 by push_cast; ring]
    have hre : r + 2 * n + 2 + β + 2 = r + 2 * n + β + 4 := by ring
    rw [hre]
    field_simp
    nlinarith
  have hh := (hs.hasSum.sub ht.hasSum).div_const (2 * (β + 2))
  rw [htel] at hh
  rw [funext heq]
  have hv : |g β r| / (2 * (β + 2) * (r + β + 2)) =
      f 0 / (2 * (β + 2)) := by
    dsimp [f]
    simp only [Nat.cast_zero, mul_zero, add_zero, div_div]
    congr 1
    ring
  rw [hv]
  exact hh

end KsIndex.PowerArc
