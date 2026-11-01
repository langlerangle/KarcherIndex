module

public import KsIndexLean.PowerArcSeedTails

@[expose] public section


/-! Explicit error bounds for mixed power-arc energy tails. -/

namespace KsIndex.PowerArc

lemma mixed_abs_summable_and_bound {β γ r t : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => |g β (r + 2 * n) * g γ (t + 2 * n)|) ∧
    (∑' n : ℕ, |g β (r + 2 * n) * g γ (t + 2 * n)|) ≤
      (energyPrimitive β r / r + energyPrimitive γ t / t) / 2 := by
  obtain ⟨hs, hb⟩ := unweighted_summable_and_bound hβ hr
  obtain ⟨hs', hb'⟩ := unweighted_summable_and_bound hγ ht
  have hp : ∀ n : ℕ, |g β (r + 2 * n) * g γ (t + 2 * n)| ≤
      (g β (r + 2 * n) ^ 2 + g γ (t + 2 * n) ^ 2) / 2 := by
    intro n
    rw [abs_mul]
    nlinarith [sq_nonneg (|g β (r + 2 * n)| - |g γ (t + 2 * n)|),
      sq_abs (g β (r + 2 * n)), sq_abs (g γ (t + 2 * n))]
  have hm := ((hs.add hs').div_const 2).of_nonneg_of_le (fun n => abs_nonneg _) hp
  refine ⟨hm, ?_⟩
  have hh := hm.tsum_le_tsum hp ((hs.add hs').div_const 2)
  rw [tsum_div_const, hs.tsum_add hs'] at hh
  linarith

lemma mixed_product_summable {β γ r t : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => g β (r + 2 * n) * g γ (t + 2 * n)) :=
  (mixed_abs_summable_and_bound hβ hγ hr ht).1.of_abs

/-- The exact leading mixed primitive leaves only a constant-weight tail.
This estimate retains that correction rather than discarding it. -/
theorem mixed_linear_tail_bound {β γ r t c : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hr : 1 ≤ r) (ht : 1 ≤ t) :
    |(∑' n : ℕ, (6 * n + c) * g β (r + 2 * n) * g γ (t + 2 * n)) -
      3 * mixedPrimitive β γ r t| ≤
      |c - 3 * (γ * r + β * t) / (β + γ)| *
        ((energyPrimitive β r / r + energyPrimitive γ t / t) / 2) := by
  let d := (γ * r + β * t) / (β + γ)
  have hp := mixed_product_summable hβ hγ hr ht
  have hw := mixed_weighted_tsum_eq hβ hγ hr ht
  have hweight : ∀ n : ℕ, (γ * (r + 2 * n) + β * (t + 2 * n)) / (β + γ) =
      d + 2 * n := by
    intro n
    dsimp [d]
    field_simp
    ring
  simp only [hweight] at hw
  have hs : Summable (fun n : ℕ => (d + 2 * n) * g β (r + 2 * n) * g γ (t + 2 * n)) := by
    exact weighted_product_summable hβ hγ hr ht d
  have hid : (∑' n : ℕ, (6 * n + c) * g β (r + 2 * n) * g γ (t + 2 * n)) =
      3 * mixedPrimitive β γ r t + (c - 3 * d) *
        ∑' n : ℕ, g β (r + 2 * n) * g γ (t + 2 * n) := by
    rw [← hw, ← tsum_mul_left, ← tsum_mul_left,
      ← (hs.mul_left 3).tsum_add (hp.mul_left (c - 3 * d))]
    apply tsum_congr
    intro n
    ring
  rw [hid, add_sub_cancel_left, abs_mul]
  have hab := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
    g β (r + 2 * n) * g γ (t + 2 * n))
    (by simpa only [Real.norm_eq_abs] using (mixed_abs_summable_and_bound hβ hγ hr ht).1)
  simp only [Real.norm_eq_abs] at hab
  have hb := hab.trans (mixed_abs_summable_and_bound hβ hγ hr ht).2
  simpa only [d, mul_div_assoc] using mul_le_mul_of_nonneg_left hb (abs_nonneg (c - 3 * d))

lemma mixed_reciprocal_summable_and_bound {β γ r t a : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) (ha : 0 < a) :
    Summable (fun n : ℕ => |g β (r + 2 * n) * g γ (t + 2 * n) / (a + 6 * n)|) ∧
    (∑' n : ℕ, |g β (r + 2 * n) * g γ (t + 2 * n) / (a + 6 * n)|) ≤
      ((energyPrimitive β r / r + energyPrimitive γ t / t) / 2) / a := by
  obtain ⟨hs, hb⟩ := mixed_abs_summable_and_bound hβ hγ hr ht
  have hp : ∀ n : ℕ, |g β (r + 2 * n) * g γ (t + 2 * n) / (a + 6 * n)| ≤
      |g β (r + 2 * n) * g γ (t + 2 * n)| / a := by
    intro n
    rw [abs_div, abs_of_pos (show 0 < a + 6 * n by positivity)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) ha
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hm := (hs.div_const a).of_nonneg_of_le (fun n => abs_nonneg _) hp
  refine ⟨hm, ?_⟩
  have hh := hm.tsum_le_tsum hp (hs.div_const a)
  rw [tsum_div_const] at hh
  exact hh.trans (div_le_div_of_nonneg_right hb ha.le)

end KsIndex.PowerArc
