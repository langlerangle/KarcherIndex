module

public import KsIndexLean.PowerArcStieltjesEnclosure
public import KsIndexLean.PowerArcNormalized

@[expose] public section


/-! Finite-prefix and shifted-tail decomposition of a power-arc Stieltjes sum. -/

namespace KsIndex.PowerArc

noncomputable def powerArcStieltjes (β r z : ℝ) : ℝ :=
  ∑' k : ℕ, ((-1 : ℝ) ^ k * g β (r + 2 * k)) / ((k : ℝ) + z)

noncomputable def normalizedStieltjesPrefix (β r z : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (-1 : ℝ) ^ k * normalizedCoefficient β r k / ((k : ℝ) + z)

theorem powerArcStieltjes_split (β r z : ℝ) (N : ℕ)
    (hβ : 0 < β) (hr : β ≤ r) (hz : 0 < z) :
    powerArcStieltjes β r z = g β r * normalizedStieltjesPrefix β r z N +
      (-1 : ℝ) ^ N * powerArcStieltjes β (r + 2 * N) (z + N) := by
  let f : ℕ → ℝ := fun k => ((-1 : ℝ) ^ k * g β (r + 2 * k)) / ((k : ℝ) + z)
  have hs0 : Summable (fun k : ℕ => (-1 : ℝ) ^ k * g β (r + 2 * k)) := by
    apply Summable.of_abs
    simpa [abs_mul, abs_pow] using abs_g_summable hβ hr
  have hs : Summable f := summable_div_nat_add hs0 hz
  have hfinite : (∑ k ∈ Finset.range N, f k) =
      g β r * normalizedStieltjesPrefix β r z N := by
    rw [normalizedStieltjesPrefix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [f]
    rw [g_eq_normalizedCoefficient hβ (by linarith : 0 ≤ r)]
    ring
  have hterm (k : ℕ) : f (k + N) = (-1 : ℝ) ^ N *
      (((-1 : ℝ) ^ k * g β ((r + 2 * N) + 2 * k)) / ((k : ℝ) + (z + N))) := by
    dsimp [f]
    rw [pow_add]
    push_cast
    rw [show r + 2 * ((k : ℝ) + N) = (r + 2 * N) + 2 * k by ring,
      show (k : ℝ) + N + z = k + (z + N) by ring]
    ring
  have htail : (∑' k, f (k + N)) =
      (-1 : ℝ) ^ N * powerArcStieltjes β (r + 2 * N) (z + N) := by
    simp only [hterm, tsum_mul_left, powerArcStieltjes]
  have hh := hs.sum_add_tsum_nat_add N
  rw [hfinite, htail] at hh
  exact hh.symm

/-- The infinite remainder after an arbitrary finite prefix has an explicit
two-term enclosure at its shifted endpoint. -/
theorem powerArcStieltjes_tail_bound (β r B z M : ℝ) (N : ℕ)
    (hβ : 0 < β) (hr : β ≤ r) (hBdef : B = (r + β + 2) / 2)
    (hz : 0 < z) (hM : 1 ≤ M) (hend : B + N + 2 ≤ M * (z + N)) :
    |powerArcStieltjes β r z - g β r * normalizedStieltjesPrefix β r z N -
      (-1 : ℝ) ^ N * (g β (r + 2 * N) / (β + 1) +
        (B - z) * (g β (r + 2 * N) / ((β + 2) * (B + N))))| ≤
      (|(B - z) * (B + 1 - z)| * M) *
        (|g β (r + 2 * N)| / ((β + 3) * (B + N) * (B + N + 1))) := by
  have hrN : β ≤ r + 2 * N := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hBN : B + N = (r + 2 * N + β + 2) / 2 := by rw [hBdef]; ring
  have hzN : 0 < z + N := by positivity
  have hh := g_stieltjes_two_term_bound β (r + 2 * N) (B + N) (z + N) M
    hβ hrN hBN hzN hM hend
  rw [show B + (N : ℝ) - (z + N) = B - z by ring,
    show B + (N : ℝ) + 1 - (z + N) = B + 1 - z by ring] at hh
  rw [powerArcStieltjes_split β r z N hβ hr hz]
  have hid : g β r * normalizedStieltjesPrefix β r z N +
      (-1 : ℝ) ^ N * powerArcStieltjes β (r + 2 * N) (z + N) -
      g β r * normalizedStieltjesPrefix β r z N -
      (-1 : ℝ) ^ N * (g β (r + 2 * N) / (β + 1) +
        (B - z) * (g β (r + 2 * N) / ((β + 2) * (B + N)))) =
      (-1 : ℝ) ^ N * (powerArcStieltjes β (r + 2 * N) (z + N) -
        g β (r + 2 * N) / (β + 1) -
        (B - z) * (g β (r + 2 * N) / ((β + 2) * (B + N)))) := by ring
  rw [hid, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact hh

end KsIndex.PowerArc
