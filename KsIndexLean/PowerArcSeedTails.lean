module

public import KsIndexLean.PowerArcRecurrence

@[expose] public section


/-! Sharper tails for the squared power-arc coefficients. -/

open Filter Topology

namespace KsIndex.PowerArc

noncomputable def squareTailPrimitive (β ξ : ℝ) : ℝ :=
  (ξ + 2 * β + 1) * g β ξ ^ 2 / (2 * (2 * β + 1))

noncomputable def squareTailError (β ξ : ℝ) : ℝ :=
  (2 * (β + 1) ^ 3) / ((2 * β + 1) * (ξ + β + 2) ^ 2)

lemma squareTailPrimitive_nonneg {β ξ : ℝ} (hβ : 0 < β) (hξ : 1 ≤ ξ) :
    0 ≤ squareTailPrimitive β ξ := by
  unfold squareTailPrimitive
  positivity

lemma squareTailPrimitive_step {β ξ : ℝ} (hβ : 0 < β) (hξ : 1 ≤ ξ) :
    squareTailPrimitive β ξ - squareTailPrimitive β (ξ + 2) =
      (1 - squareTailError β ξ) * g β ξ ^ 2 := by
  have hd : ξ + β + 2 ≠ 0 := by linarith
  have hb : 2 * β + 1 ≠ 0 := by linarith
  have hg : g β (ξ + 2) = (β - ξ) * g β ξ / (ξ + β + 2) := by
    apply (eq_div_iff hd).mpr
    nlinarith [g_step_two hβ ξ]
  rw [squareTailPrimitive, squareTailPrimitive, hg, squareTailError]
  field_simp
  ring

lemma squareTailPrimitive_le_square {β ξ : ℝ} (hβ : 0 < β) (hξ : 1 ≤ ξ) :
    squareTailPrimitive β ξ ≤ ((ξ + β) * g β ξ) ^ 2 := by
  unfold squareTailPrimitive
  apply (div_le_iff₀ (by positivity : 0 < 2 * (2 * β + 1))).mpr
  have hx : 1 ≤ ξ + β := by linarith
  have h1 : ξ + 2 * β + 1 ≤ 2 * (ξ + β) := by linarith
  have h2 : ξ + β ≤ (ξ + β) ^ 2 := by nlinarith
  have h3 : ξ + 2 * β + 1 ≤ 2 * (2 * β + 1) * (ξ + β) ^ 2 := by
    nlinarith [sq_nonneg (ξ + β)]
  have hh := mul_le_mul_of_nonneg_right h3 (sq_nonneg (g β ξ))
  nlinarith

lemma squareTailPrimitive_tendsto_zero {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => squareTailPrimitive β (r + 2 * n)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => squareTailPrimitive_nonneg hβ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    (fun n => squareTailPrimitive_le_square hβ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  simpa using (weighted_factor_tendsto_zero hβ hr).pow 2

lemma squareTailError_nonneg {β ξ : ℝ} (hβ : 0 < β) :
    0 ≤ squareTailError β ξ := by
  unfold squareTailError
  positivity

lemma squareTailError_le {β r ξ : ℝ} (hβ : 0 < β) (hr : 1 ≤ r) (hξ : r ≤ ξ) :
    squareTailError β ξ ≤ squareTailError β r := by
  unfold squareTailError
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hsq : (r + β + 2) ^ 2 ≤ (ξ + β + 2) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- The squared tail is at least its explicit primitive and at most the
primitive divided by `1 - squareTailError β r`. The correction is nonnegative. -/
theorem square_tail_bounds {β r : ℝ} (hβ : 0 < β) (hr : 1 ≤ r)
    (he : squareTailError β r < 1) :
    squareTailPrimitive β r ≤ ∑' n : ℕ, g β (r + 2 * n) ^ 2 ∧
    (∑' n : ℕ, g β (r + 2 * n) ^ 2) ≤
      squareTailPrimitive β r / (1 - squareTailError β r) := by
  have hs := (unweighted_summable_and_bound hβ hr).1
  have hp : ∀ n : ℕ, squareTailError β (r + 2 * n) * g β (r + 2 * n) ^ 2 ≤
      squareTailError β r * g β (r + 2 * n) ^ 2 := by
    intro n
    exact mul_le_mul_of_nonneg_right
      (squareTailError_le hβ hr (by linarith [Nat.cast_nonneg (α := ℝ) n])) (sq_nonneg _)
  have hc := (hs.mul_left (squareTailError β r)).of_nonneg_of_le
    (fun n => mul_nonneg (squareTailError_nonneg hβ) (sq_nonneg _)) hp
  have hd := hs.sub hc
  have hfinite : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (g β (r + 2 * n) ^ 2 -
        squareTailError β (r + 2 * n) * g β (r + 2 * n) ^ 2)) =
      squareTailPrimitive β r - squareTailPrimitive β (r + 2 * N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hh := squareTailPrimitive_step hβ
        (show 1 ≤ r + 2 * N by linarith [Nat.cast_nonneg (α := ℝ) N])
      push_cast
      rw [show r + 2 * ((N : ℝ) + 1) = (r + 2 * N) + 2 by ring]
      linarith
  have hl := (tendsto_const_nhds (x := squareTailPrimitive β r)).sub
    (squareTailPrimitive_tendsto_zero hβ hr)
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (g β (r + 2 * n) ^ 2 - squareTailError β (r + 2 * n) * g β (r + 2 * n) ^ 2))
      atTop (𝓝 (squareTailPrimitive β r)) := by
    simpa only [hfinite, sub_zero] using hl
  have hid := tendsto_nhds_unique hd.hasSum.tendsto_sum_nat hlim
  rw [hs.tsum_sub hc] at hid
  have hnonneg : 0 ≤ ∑' n : ℕ, squareTailError β (r + 2 * n) * g β (r + 2 * n) ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (squareTailError_nonneg hβ) (sq_nonneg _))
  have hub := hc.tsum_le_tsum hp (hs.mul_left (squareTailError β r))
  rw [tsum_mul_left] at hub
  refine ⟨by linarith, (le_div_iff₀ (by linarith : 0 < 1 - squareTailError β r)).mpr ?_⟩
  nlinarith

end KsIndex.PowerArc
