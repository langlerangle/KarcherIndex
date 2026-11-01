module

public import KsIndexLean.PowerArcWeightedAbsoluteTails

@[expose] public section


/-! Weighted absolute tails with a shifted sampling coordinate.

Comparison with the exact telescoping denominators yields rational endpoint
bounds without fractional-power envelope estimates.
-/
namespace KsIndex.PowerArc

theorem abs_g_over_shifted_linear_bound (β r X : ℝ) (hβ : 0 < β) (hr : β ≤ r)
    (hX : r + β + 2 ≤ X) :
    Summable (fun n : ℕ => |g β (r+2*n)| / (X+2*n)) ∧
      (∑' n : ℕ, |g β (r+2*n)| / (X+2*n)) ≤ |g β r| / (2*(β+1)) := by
  have hs := abs_g_over_linear_hasSum hβ hr
  have hn (n : ℕ) : 0 ≤ |g β (r+2*n)| / (X+2*n) := by
    have hx : 0 < X := by linarith
    positivity
  have hm (n : ℕ) : |g β (r+2*n)| / (X+2*n) ≤
      |g β (r+2*n)| / (r+2*n+β+2) := by
    have hd : 0 < r+2*n+β+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hd (by linarith)
  have ht := hs.summable.of_nonneg_of_le hn hm
  exact ⟨ht, (ht.tsum_le_tsum hm hs.summable).trans_eq hs.tsum_eq⟩

theorem abs_g_over_shifted_square_bound (β r X : ℝ) (hβ : 0 < β) (hr : β ≤ r)
    (hX : r + β + 4 ≤ X) :
    Summable (fun n : ℕ => |g β (r+2*n)| / (X+2*n)^2) ∧
      (∑' n : ℕ, |g β (r+2*n)| / (X+2*n)^2) ≤
        |g β r| / (2*(β+2)*(r+β+2)) := by
  have hs := abs_g_over_two_linear_hasSum hβ hr
  have hn (n : ℕ) : 0 ≤ |g β (r+2*n)| / (X+2*n)^2 := by positivity
  have hm (n : ℕ) : |g β (r+2*n)| / (X+2*n)^2 ≤
      |g β (r+2*n)| / ((r+2*n+β+2)*(r+2*n+β+4)) := by
    have hd : 0 < r+2*n+β+2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have he : 0 < r+2*n+β+4 := by linarith
    have hx : 0 < X+2*n := by linarith
    apply div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hd he)
    have hh := mul_le_mul (show r+2*n+β+2 ≤ X+2*n by linarith)
      (show r+2*n+β+4 ≤ X+2*n by linarith) he.le hx.le
    simpa only [pow_two] using hh
  have ht := hs.summable.of_nonneg_of_le hn hm
  exact ⟨ht, (ht.tsum_le_tsum hm hs.summable).trans_eq hs.tsum_eq⟩

end KsIndex.PowerArc
