module

public import KsIndexLean.PowerArcWeightedAbsoluteTails

@[expose] public section


/-! Rational comparison factors for weighted absolute power-arc tails. -/
namespace KsIndex.PowerArc

/-- A constant denominator comparison handles positive as well as negative shifts. -/
theorem abs_g_over_scaled_linear_bound (β r X c : ℝ)
    (hβ : 0 < β) (hr : β ≤ r) (hX : 0 < X) (hc : 1 ≤ c)
    (hcomp : r+β+2 ≤ c*X) :
    Summable (fun k : ℕ => |g β (r+2*k)|/(X+2*k)) ∧
      (∑' k : ℕ, |g β (r+2*k)|/(X+2*k)) ≤ c*|g β r|/(2*(β+1)) := by
  have hs := (abs_g_over_linear_hasSum hβ hr).summable.mul_left c
  have hm (k : ℕ) : |g β (r+2*k)|/(X+2*k) ≤
      c*(|g β (r+2*k)|/(r+2*k+β+2)) := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hx : 0 < X+2*k := by positivity
    have hd : 0 < r+2*k+β+2 := by linarith
    have hb : r+2*k+β+2 ≤ c*(X+2*k) := by nlinarith
    rw [← mul_div_assoc, div_le_div_iff₀ hx hd]
    nlinarith [mul_le_mul_of_nonneg_left hb (abs_nonneg (g β (r+2*k)))]
  have ht := hs.of_nonneg_of_le (fun _ => by positivity) hm
  refine ⟨ht, (ht.tsum_le_tsum hm hs).trans_eq ?_⟩
  rw [tsum_mul_left, (abs_g_over_linear_hasSum hβ hr).tsum_eq]
  ring

/-- Two denominator comparisons give a squared-weight tail bound. -/
theorem abs_g_over_scaled_square_bound (β r X c : ℝ)
    (hβ : 0 < β) (hr : β ≤ r) (hX : 0 < X) (hc : 1 ≤ c)
    (hcomp : r+β+4 ≤ c*X) :
    Summable (fun k : ℕ => |g β (r+2*k)|/(X+2*k)^2) ∧
      (∑' k : ℕ, |g β (r+2*k)|/(X+2*k)^2) ≤
        c^2*|g β r|/(2*(β+2)*(r+β+2)) := by
  have hs := (abs_g_over_two_linear_hasSum hβ hr).summable.mul_left (c^2)
  have hm (k : ℕ) : |g β (r+2*k)|/(X+2*k)^2 ≤
      c^2*(|g β (r+2*k)|/((r+2*k+β+2)*(r+2*k+β+4))) := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    have hx : 0 < X+2*k := by positivity
    have hd : 0 < r+2*k+β+2 := by linarith
    have he : 0 < r+2*k+β+4 := by linarith
    have hb : r+2*k+β+4 ≤ c*(X+2*k) := by nlinarith
    have hd' : r+2*k+β+2 ≤ c*(X+2*k) := by linarith
    have hprod := mul_le_mul hd' hb he.le (by positivity : 0 ≤ c*(X+2*k))
    rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hx) (mul_pos hd he)]
    nlinarith [mul_le_mul_of_nonneg_left hprod (abs_nonneg (g β (r+2*k)))]
  have ht := hs.of_nonneg_of_le (fun _ => by positivity) hm
  refine ⟨ht, (ht.tsum_le_tsum hm hs).trans_eq ?_⟩
  rw [tsum_mul_left, (abs_g_over_two_linear_hasSum hβ hr).tsum_eq]
  ring

end KsIndex.PowerArc
