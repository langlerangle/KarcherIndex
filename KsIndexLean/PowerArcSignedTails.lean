module

public import KsIndexLean.PowerArcRecurrence

@[expose] public section


/-! Exact signed tails for convolution of power-arc coefficients. -/

namespace KsIndex.PowerArc
open Filter Topology

lemma abs_g_step {β ξ : ℝ} (hβ : 0 < β) (hξ : β ≤ ξ) :
    (ξ + β + 2) * |g β (ξ + 2)| = (ξ - β) * |g β ξ| := by
  have hh := congrArg abs (g_step_two hβ ξ)
  rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < ξ + β + 2),
    abs_of_nonpos (by linarith : β - ξ ≤ 0)] at hh
  simpa only [neg_sub] using hh

lemma abs_g_summable {β r : ℝ} (hβ : 0 < β) (hr : β ≤ r) :
    Summable (fun n : ℕ => |g β (r + 2 * n)|) := by
  apply summable_of_sum_range_le (fun n => abs_nonneg _) (c := (r + β) * |g β r| / (2 * β))
  intro N
  have htel : ∀ N : ℕ, (2 * β) * (∑ n ∈ Finset.range N, |g β (r + 2 * n)|) =
      (r + β) * |g β r| - (r + 2 * N + β) * |g β (r + 2 * N)| := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hh := abs_g_step hβ (show β ≤ r + 2 * N by
        linarith [Nat.cast_nonneg (α := ℝ) N])
      push_cast
      rw [show r + 2 * ((N : ℝ) + 1) = (r + 2 * N) + 2 by ring]
      nlinarith
  apply (le_div_iff₀ (by positivity : 0 < 2 * β)).mpr
  have hn : 0 ≤ r + 2 * N + β := by linarith [Nat.cast_nonneg (α := ℝ) N]
  nlinarith [htel N, mul_nonneg hn (abs_nonneg (g β (r + 2 * N)))]

noncomputable def signedTailPrimitive (β r : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * ((r + 2 * n + β) * g β (r + 2 * n)) / (2 * β)

lemma signedTailPrimitive_step {β r : ℝ} (hβ : 0 < β) (n : ℕ) :
    signedTailPrimitive β r n - signedTailPrimitive β r (n + 1) =
      (-1 : ℝ) ^ n * g β (r + 2 * n) := by
  have hh := g_step_two hβ (r + 2 * n)
  simp only [signedTailPrimitive, pow_succ, Nat.cast_add, Nat.cast_one]
  rw [show r + 2 * ((n : ℝ) + 1) = (r + 2 * n) + 2 by ring]
  field_simp
  linear_combination hh

lemma signedTailPrimitive_tendsto_zero {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    Tendsto (signedTailPrimitive β r) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hh := (weighted_factor_tendsto_zero hβ hr).abs.div_const (2 * β)
  simpa only [Function.comp_def, signedTailPrimitive, abs_div, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow, one_mul, abs_of_pos (by positivity : 0 < 2 * β),
    abs_zero, zero_div] using hh

/-- Exact leading tail used in the transposed convolution. -/
theorem signed_g_tsum {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) (hrβ : β ≤ r) :
    (∑' n : ℕ, (-1 : ℝ) ^ n * g β (r + 2 * n)) =
      (r + β) * g β r / (2 * β) := by
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ n * g β (r + 2 * n)) := by
    apply Summable.of_abs
    simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
      abs_g_summable hβ hrβ
  have hf : ∀ N : ℕ, (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * g β (r + 2 * n)) =
      signedTailPrimitive β r 0 - signedTailPrimitive β r N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, ← signedTailPrimitive_step hβ N]
      ring
  have hl := (tendsto_const_nhds (x := signedTailPrimitive β r 0)).sub
    (signedTailPrimitive_tendsto_zero hβ hr)
  have hl' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (-1 : ℝ) ^ n * g β (r + 2 * n)) atTop (𝓝 (signedTailPrimitive β r 0)) := by
    simpa only [hf, sub_zero] using hl
  have hh := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hl'
  simpa [signedTailPrimitive] using hh

end KsIndex.PowerArc
