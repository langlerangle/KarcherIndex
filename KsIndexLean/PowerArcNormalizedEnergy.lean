module

public import KsIndexLean.PowerArcNormalized

@[expose] public section


/-! Weighted energy estimates for normalized power-arc coefficients.

The proof uses their recurrence directly and does not require a nonvanishing
hypothesis on an unnormalized Fourier coefficient.
-/

namespace KsIndex.PowerArc

theorem normalized_energy_step (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (n : ℕ) :
    ((r + 2 * n + β) * normalizedCoefficient β r n) ^ 2 / (4 * β) -
      ((r + 2 * (n + 1) + β) * normalizedCoefficient β r (n + 1)) ^ 2 / (4 * β) =
      (r + 2 * n) * normalizedCoefficient β r n ^ 2 := by
  have hb : β ≠ 0 := ne_of_gt hβ
  have hd : r + 2 * n + β + 2 ≠ 0 := by positivity
  rw [normalizedCoefficient]
  rw [show r + 2 * ((n : ℝ) + 1) + β = r + 2 * n + β + 2 by ring]
  field_simp
  ring

theorem normalized_weighted_sum_range (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) (N : ℕ) :
    (∑ n ∈ Finset.range N, (r + 2 * n) * normalizedCoefficient β r n ^ 2) =
      (r + β) ^ 2 / (4 * β) -
        ((r + 2 * N + β) * normalizedCoefficient β r N) ^ 2 / (4 * β) := by
  induction N with
  | zero => simp [normalizedCoefficient]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hh := normalized_energy_step β r hβ hr N
    push_cast
    linarith

theorem normalized_weighted_summable_bound (β r : ℝ) (hβ : 0 < β) (hr : 0 ≤ r) :
    Summable (fun n : ℕ => (r + 2 * n) * normalizedCoefficient β r n ^ 2) ∧
      (∑' n : ℕ, (r + 2 * n) * normalizedCoefficient β r n ^ 2) ≤
        (r + β) ^ 2 / (4 * β) := by
  have hn (n : ℕ) : 0 ≤ (r + 2 * n) * normalizedCoefficient β r n ^ 2 := by positivity
  have hb (N : ℕ) :
      (∑ n ∈ Finset.range N, (r + 2 * n) * normalizedCoefficient β r n ^ 2) ≤
        (r + β) ^ 2 / (4 * β) := by
    rw [normalized_weighted_sum_range β r hβ hr]
    exact sub_le_self _ (by positivity)
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

/-- A pointwise normalized-coefficient bound yields a weighted infinite energy
bound, including summability. -/
theorem normalized_envelope_energy (β r C M a b : ℝ) (f : ℕ → ℝ)
    (hβ : 0 < β) (hr : 0 ≤ r) (hM : 0 ≤ M) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M * r) (hbM : b ≤ 2 * M)
    (hf : ∀ n, |f n| ≤ C * |normalizedCoefficient β r n|) :
    Summable (fun n : ℕ => (a + b * n) * f n ^ 2) ∧
      (∑' n : ℕ, (a + b * n) * f n ^ 2) ≤
        (C ^ 2 * M) * ((r + β) ^ 2 / (4 * β)) := by
  have hmajor (n : ℕ) : (a + b * n) * f n ^ 2 ≤
      (C ^ 2 * M) * ((r + 2 * n) * normalizedCoefficient β r n ^ 2) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hw : a + b * n ≤ M * (r + 2 * n) := by
      nlinarith [mul_le_mul_of_nonneg_right hbM hn]
    have hs : f n ^ 2 ≤ C ^ 2 * normalizedCoefficient β r n ^ 2 := by
      have hh := sq_le_sq₀ (abs_nonneg (f n)) ((abs_nonneg (f n)).trans (hf n))
      have hh' := hh.mpr (hf n)
      simpa only [mul_pow, sq_abs] using hh'
    calc
      _ ≤ (a + b * n) * (C ^ 2 * normalizedCoefficient β r n ^ 2) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (M * (r + 2 * n)) * (C ^ 2 * normalizedCoefficient β r n ^ 2) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
      _ = _ := by ring
  have hbase := normalized_weighted_summable_bound β r hβ hr
  have hsum := hbase.1.mul_left (C ^ 2 * M)
  have hnonneg (n : ℕ) : 0 ≤ (a + b * n) * f n ^ 2 := by positivity
  have hs := hsum.of_nonneg_of_le hnonneg hmajor
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (C ^ 2 * M) * ((r + 2 * n) * normalizedCoefficient β r n ^ 2) :=
      hs.tsum_le_tsum hmajor hsum
    _ = (C ^ 2 * M) * (∑' n : ℕ, (r + 2 * n) * normalizedCoefficient β r n ^ 2) :=
      tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase.2 (by positivity)

end KsIndex.PowerArc
