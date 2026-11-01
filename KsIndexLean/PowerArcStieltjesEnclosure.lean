module

public import KsIndexLean.PowerArcThirdWeightedTail
public import KsIndexLean.StieltjesExpansionBound

@[expose] public section


/-! An explicit rational enclosure of a power-arc Stieltjes tail. -/

namespace KsIndex.PowerArc

theorem g_stieltjes_two_term_bound (β r B z M : ℝ)
    (hβ : 0 < β) (hr : β ≤ r) (hBdef : B = (r + β + 2) / 2)
    (hz : 0 < z) (hM : 1 ≤ M) (hend : B + 2 ≤ M * z) :
    |(∑' k : ℕ, ((-1 : ℝ) ^ k * g β (r + 2 * k)) / ((k : ℝ) + z)) -
        g β r / (β + 1) - (B - z) * (g β r / ((β + 2) * B))| ≤
      (|(B - z) * (B + 1 - z)| * M) *
        (|g β r| / ((β + 3) * B * (B + 1))) := by
  let e : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * g β (r + 2 * k)
  let A := B - β - 1
  have hB : 0 < B := by rw [hBdef]; linarith
  have he : Summable e := by
    apply Summable.of_abs
    simpa [e, abs_mul, abs_pow] using abs_g_summable hβ hr
  have hrec (k : ℕ) : ((k : ℝ) + B) * e (k + 1) = ((k : ℝ) + A) * e k := by
    have hh := g_step_two hβ (r + 2 * k)
    dsimp [e, A]
    rw [hBdef, pow_succ]
    push_cast
    rw [show r + 2 * ((k : ℝ) + 1) = (r + 2 * k) + 2 by ring]
    linear_combination -((-1 : ℝ) ^ k) / 2 * hh
  have hthird : HasSum (fun k : ℕ => |e k| /
      (((k : ℝ) + B) * ((k : ℝ) + B + 1) * ((k : ℝ) + B + 2)))
      (|g β r| / ((β + 3) * B * (B + 1))) := by
    have hscaled := (abs_g_over_three_linear_hasSum hβ hr).mul_left (8 : ℝ)
    have hfun : (fun k : ℕ => |e k| /
        (((k : ℝ) + B) * ((k : ℝ) + B + 1) * ((k : ℝ) + B + 2))) =
        (fun k : ℕ => 8 * (|g β (r + 2 * k)| /
          ((r + 2 * k + β + 2) * (r + 2 * k + β + 4) * (r + 2 * k + β + 6)))) := by
      funext k
      dsimp [e]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      rw [hBdef]
      field_simp
      ring
    have hv : |g β r| / ((β + 3) * B * (B + 1)) =
        8 * (|g β r| / (2 * (β + 3) * (r + β + 2) * (r + β + 4))) := by
      rw [hBdef]
      field_simp
      ring
    rw [hfun, hv]
    exact hscaled
  have hgap : B - A = β + 1 := by dsimp [A]; ring
  have hgap1 : B + 1 - A = β + 2 := by dsimp [A]; ring
  have hg0 : B - A ≠ 0 := by rw [hgap]; positivity
  have hg1 : B + 1 - A ≠ 0 := by rw [hgap1]; positivity
  have hh := stieltjes_two_term_tsum_bound he A B z M
    (|g β r| / ((β + 3) * B * (B + 1))) hB hz hg0 hg1 hM hend hrec hthird
  simpa only [e, hgap, hgap1, pow_zero, Nat.cast_zero, mul_zero, add_zero, one_mul] using hh

end KsIndex.PowerArc
