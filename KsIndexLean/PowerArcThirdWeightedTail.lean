module

public import KsIndexLean.PowerArcWeightedAbsoluteTails

@[expose] public section


/-! A third rationally weighted power-arc tail.

This exact endpoint formula controls the remainder after two terms of a
Stieltjes expansion. No asymptotic approximation is used.
-/

namespace KsIndex.PowerArc

theorem abs_g_over_three_linear_hasSum {β r : ℝ} (hβ : 0 < β) (hr : β ≤ r) :
    HasSum (fun n : ℕ => |g β (r + 2 * n)| /
      ((r + 2 * n + β + 2) * (r + 2 * n + β + 4) * (r + 2 * n + β + 6)))
      (|g β r| / (2 * (β + 3) * (r + β + 2) * (r + β + 4))) := by
  let f : ℕ → ℝ := fun n => |g β (r + 2 * n)| /
    ((r + 2 * n + β + 2) * (r + 2 * n + β + 4))
  have hs : Summable f := (abs_g_over_two_linear_hasSum hβ hr).summable
  have ht : Summable (fun n => f (n + 1)) := (summable_nat_add_iff 1).2 hs
  have htel : (∑' n, f n) - (∑' n, f (n + 1)) = f 0 := by
    have hh := hs.tsum_eq_zero_add
    linarith
  have heq (n : ℕ) : |g β (r + 2 * n)| /
      ((r + 2 * n + β + 2) * (r + 2 * n + β + 4) * (r + 2 * n + β + 6)) =
      (f n - f (n + 1)) / (2 * (β + 3)) := by
    have hn : β ≤ r + 2 * n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hd : 0 < r + 2 * n + β + 2 := by linarith
    have he : 0 < r + 2 * n + β + 4 := by linarith
    have hf : 0 < r + 2 * n + β + 6 := by linarith
    have hb : 0 < β + 3 := by linarith
    have hh := abs_g_step hβ hn
    dsimp [f]
    rw [show r + 2 * ((n + 1 : ℕ) : ℝ) = (r + 2 * n) + 2 by push_cast; ring]
    rw [show r + 2 * n + 2 + β + 2 = r + 2 * n + β + 4 by ring,
      show r + 2 * n + 2 + β + 4 = r + 2 * n + β + 6 by ring]
    field_simp
    nlinarith
  have hh := (hs.hasSum.sub ht.hasSum).div_const (2 * (β + 3))
  rw [htel] at hh
  rw [funext heq]
  have hv : |g β r| / (2 * (β + 3) * (r + β + 2) * (r + β + 4)) =
      f 0 / (2 * (β + 3)) := by
    dsimp [f]
    simp only [Nat.cast_zero, mul_zero, add_zero, div_div]
    congr 1
    ring
  rw [hv]
  exact hh

end KsIndex.PowerArc
