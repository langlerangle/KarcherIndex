module

public import KsIndexLean.PowerArcMixedTails

@[expose] public section


/-! Mixed power-arc tails with independently scaled coefficient families. -/

namespace KsIndex.PowerArc

/-- Scaling each family before the square estimate avoids cross-family seed ratios. -/
lemma scaled_mixed_abs_summable_and_bound {β γ r t : ℝ} (u v : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => |(u * g β (r + 2 * n)) * (v * g γ (t + 2 * n))|) ∧
    (∑' n : ℕ, |(u * g β (r + 2 * n)) * (v * g γ (t + 2 * n))|) ≤
      (u ^ 2 * (energyPrimitive β r / r) + v ^ 2 * (energyPrimitive γ t / t)) / 2 := by
  obtain ⟨hs, hb⟩ := unweighted_summable_and_bound hβ hr
  obtain ⟨hs', hb'⟩ := unweighted_summable_and_bound hγ ht
  have hp : ∀ n : ℕ, |(u * g β (r + 2 * n)) * (v * g γ (t + 2 * n))| ≤
      (u ^ 2 * g β (r + 2 * n) ^ 2 + v ^ 2 * g γ (t + 2 * n) ^ 2) / 2 := by
    intro n
    rw [abs_mul]
    nlinarith [sq_nonneg (|u * g β (r + 2 * n)| - |v * g γ (t + 2 * n)|),
      sq_abs (u * g β (r + 2 * n)), sq_abs (v * g γ (t + 2 * n))]
  have hs2 := hs.mul_left (u ^ 2)
  have ht2 := hs'.mul_left (v ^ 2)
  have hm := ((hs2.add ht2).div_const 2).of_nonneg_of_le (fun n => abs_nonneg _) hp
  refine ⟨hm, ?_⟩
  have hh := hm.tsum_le_tsum hp ((hs2.add ht2).div_const 2)
  rw [tsum_div_const, hs2.tsum_add ht2, tsum_mul_left, tsum_mul_left] at hh
  have hu := mul_le_mul_of_nonneg_left hb (sq_nonneg u)
  have hv := mul_le_mul_of_nonneg_left hb' (sq_nonneg v)
  linarith

lemma scaled_mixed_linear_summable {β γ r t c : ℝ} (u v : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    Summable (fun n : ℕ => (6 * n + c) * (u * g β (r + 2 * n)) *
      (v * g γ (t + 2 * n))) := by
  have h := (weighted_product_summable hβ hγ hr ht (c / 3)).mul_left (3 * u * v)
  apply h.congr
  intro n
  ring

/-- The weighted tail retains its exact mixed primitive after independent scaling. -/
theorem scaled_mixed_linear_tail_bound {β γ r t c : ℝ} (u v : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    |(∑' n : ℕ, (6 * n + c) * (u * g β (r + 2 * n)) *
        (v * g γ (t + 2 * n))) - 3 * (u * v * mixedPrimitive β γ r t)| ≤
      |c - 3 * (γ * r + β * t) / (β + γ)| *
        ((u ^ 2 * (energyPrimitive β r / r) +
          v ^ 2 * (energyPrimitive γ t / t)) / 2) := by
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
  have hs := weighted_product_summable hβ hγ hr ht d
  have hid : (∑' n : ℕ, (6 * n + c) * (u * g β (r + 2 * n)) *
        (v * g γ (t + 2 * n))) =
      3 * (u * v * mixedPrimitive β γ r t) + (c - 3 * d) *
        ∑' n : ℕ, (u * g β (r + 2 * n)) * (v * g γ (t + 2 * n)) := by
    simp_rw [show ∀ n : ℕ, (u * g β (r + 2 * n)) * (v * g γ (t + 2 * n)) =
      (u * v) * (g β (r + 2 * n) * g γ (t + 2 * n)) by intro n; ring]
    rw [tsum_mul_left]
    calc
      _ = ∑' n : ℕ, ((3 * (u * v)) *
          ((d + 2 * n) * g β (r + 2 * n) * g γ (t + 2 * n)) +
          ((c - 3 * d) * (u * v)) * (g β (r + 2 * n) * g γ (t + 2 * n))) := by
        apply tsum_congr
        intro n
        ring
      _ = _ := by
        rw [(hs.mul_left (3 * (u * v))).tsum_add (hp.mul_left ((c - 3 * d) * (u * v))),
          tsum_mul_left, tsum_mul_left, hw]
        ring
  rw [hid, add_sub_cancel_left, abs_mul]
  obtain ⟨ha, hb⟩ := scaled_mixed_abs_summable_and_bound u v hβ hγ hr ht
  have hab := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
    (u * g β (r + 2 * n)) * (v * g γ (t + 2 * n))) (by simpa only [Real.norm_eq_abs] using ha)
  simp only [Real.norm_eq_abs] at hab
  have hh := mul_le_mul_of_nonneg_left (hab.trans hb) (abs_nonneg (c - 3 * d))
  simpa only [d, mul_div_assoc] using hh

/-- Reciprocal-weight errors are controlled by the same independently scaled mass. -/
lemma scaled_mixed_reciprocal_summable_and_bound {β γ r t a : ℝ} (u v : ℝ)
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) (ha : 0 < a) :
    Summable (fun n : ℕ => |(u * g β (r + 2 * n)) *
      (v * g γ (t + 2 * n)) / (a + 6 * n)|) ∧
    (∑' n : ℕ, |(u * g β (r + 2 * n)) * (v * g γ (t + 2 * n)) / (a + 6 * n)|) ≤
      ((u ^ 2 * (energyPrimitive β r / r) +
        v ^ 2 * (energyPrimitive γ t / t)) / 2) / a := by
  obtain ⟨hs, hb⟩ := scaled_mixed_abs_summable_and_bound u v hβ hγ hr ht
  have hp : ∀ n : ℕ, |(u * g β (r + 2 * n)) * (v * g γ (t + 2 * n)) /
      (a + 6 * n)| ≤ |(u * g β (r + 2 * n)) * (v * g γ (t + 2 * n))| / a := by
    intro n
    rw [abs_div, abs_of_pos (show 0 < a + 6 * n by positivity)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) ha
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hm := (hs.div_const a).of_nonneg_of_le (fun n => abs_nonneg _) hp
  refine ⟨hm, ?_⟩
  have hh := hm.tsum_le_tsum hp (hs.div_const a)
  rw [tsum_div_const] at hh
  exact hh.trans (div_le_div_of_nonneg_right hb ha.le)

lemma normalized_energy_mass (β r : ℝ) :
    (g β 0)⁻¹ ^ 2 * (energyPrimitive β r / r) =
      ((r + β) * (g β r / g β 0)) ^ 2 / (4 * β * r) := by
  simp only [energyPrimitive, div_eq_mul_inv, mul_inv_rev]
  ring

lemma normalized_mixed_primitive (β γ r t : ℝ) :
    (g β 0)⁻¹ * (g γ 0)⁻¹ * mixedPrimitive β γ r t =
      ((r + β) * (g β r / g β 0)) * ((t + γ) * (g γ t / g γ 0)) /
        (2 * (β + γ)) := by
  simp only [mixedPrimitive, div_eq_mul_inv]
  ring

/-- Each family's zero-frequency seed normalizes only that family. -/
theorem normalized_mixed_linear_tail_bound {β γ r t c : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    |(∑' n : ℕ, (6 * n + c) * (g β (r + 2 * n) / g β 0) *
        (g γ (t + 2 * n) / g γ 0)) -
      3 * (((r + β) * (g β r / g β 0)) * ((t + γ) * (g γ t / g γ 0)) /
        (2 * (β + γ)))| ≤
      |c - 3 * (γ * r + β * t) / (β + γ)| *
        ((((r + β) * (g β r / g β 0)) ^ 2 / (4 * β * r) +
          ((t + γ) * (g γ t / g γ 0)) ^ 2 / (4 * γ * t)) / 2) := by
  have h := scaled_mixed_linear_tail_bound ((g β 0)⁻¹) ((g γ 0)⁻¹) hβ hγ hr ht (c := c)
  rw [normalized_mixed_primitive, normalized_energy_mass, normalized_energy_mass] at h
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end KsIndex.PowerArc

