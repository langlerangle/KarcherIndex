module

public import KsIndexLean.PowerArcSeedScale

@[expose] public section


/-! Exact rational arithmetic for normalized power-arc sums. -/

namespace KsIndex.PowerArc

def rationalCoefficient (β r : ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => (β - (r + 2 * n)) / (r + 2 * n + β + 2) *
      rationalCoefficient β r n

lemma rationalCoefficient_cast (β r : ℚ) (n : ℕ) :
    (rationalCoefficient β r n : ℝ) = normalizedCoefficient β r n := by
  induction n with
  | zero => simp [rationalCoefficient, normalizedCoefficient]
  | succ n ih =>
    simp only [rationalCoefficient, normalizedCoefficient]
    push_cast
    rw [ih]

def rationalPartial (β r : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, rationalCoefficient β r n ^ 2

def rationalTail (β r : ℚ) (N : ℕ) : ℚ :=
  (r + 2 * N + 2 * β + 1) * rationalCoefficient β r N ^ 2 / (2 * (2 * β + 1))

def rationalError (β r : ℚ) (N : ℕ) : ℚ :=
  2 * (β + 1) ^ 3 / ((2 * β + 1) * (r + 2 * N + β + 2) ^ 2)

def rationalLower (β r : ℚ) (N : ℕ) : ℚ := rationalPartial β r N + rationalTail β r N

def rationalUpper (β r : ℚ) (N : ℕ) : ℚ :=
  rationalPartial β r N + rationalTail β r N / (1 - rationalError β r N)

lemma rationalError_cast (β r : ℚ) (N : ℕ) :
    (rationalError β r N : ℝ) = squareTailError β (r + 2 * N) := by
  simp only [rationalError, squareTailError]
  push_cast
  rfl

theorem rational_sum_bounds (β : ℚ) (r : ℤ) (N : ℕ)
    (hβ : 0 < β) (hr : 0 ≤ r) (hg : g β r ≠ 0)
    (hN : 1 ≤ (r : ℚ) + 2 * N) (he : rationalError β r N < 1) :
    (rationalLower β r N : ℝ) ≤ ∑' n : ℕ, normalizedCoefficient β r n ^ 2 ∧
    (∑' n : ℕ, normalizedCoefficient β r n ^ 2) ≤ (rationalUpper β r N : ℝ) := by
  have hb := normalized_tail_bounds (β := (β : ℝ)) (r := (r : ℝ))
    (by exact_mod_cast hβ) (by exact_mod_cast hr) hg N
    (by exact_mod_cast hN) (by
      have hh : (rationalError β r N : ℝ) < 1 := by exact_mod_cast he
      rw [rationalError_cast] at hh
      simpa only [Rat.cast_intCast] using hh)
  have hs := normalized_sq_summable (β := (β : ℝ)) (by exact_mod_cast hβ) r hr hg
  have hsplit := hs.sum_add_tsum_nat_add N
  have hpartial : (rationalPartial β r N : ℝ) =
      ∑ n ∈ Finset.range N, normalizedCoefficient β r n ^ 2 := by
    simp only [rationalPartial]
    push_cast
    simp only [rationalCoefficient_cast, Rat.cast_intCast]
  have htail : (rationalTail β r N : ℝ) =
      (r + 2 * N + 2 * (β : ℝ) + 1) * normalizedCoefficient β r N ^ 2 /
        (2 * (2 * (β : ℝ) + 1)) := by
    simp only [rationalTail]
    push_cast
    simp only [rationalCoefficient_cast, Rat.cast_intCast]
  have herr := rationalError_cast β (r : ℚ) N
  simp only [Rat.cast_intCast] at herr
  simp only [rationalLower, rationalUpper]
  push_cast
  rw [hpartial, htail, herr]
  dsimp only at hb
  have hcomm : (∑' n : ℕ, normalizedCoefficient (β : ℝ) r (N + n) ^ 2) =
      ∑' n : ℕ, normalizedCoefficient (β : ℝ) r (n + N) ^ 2 := by
    simp only [Nat.add_comm]
  rw [hcomm] at hb
  constructor <;> linarith [hb.1, hb.2]

theorem seed_ratio_bounds_of_sum_bounds {β a b c d : ℝ} (hβ : 0 < β)
    (ha : 0 ≤ 2 * a - 1) (hc : 0 < c)
    (he : a ≤ ∑' n : ℕ, normalizedCoefficient β 0 n ^ 2)
    (he' : (∑' n : ℕ, normalizedCoefficient β 0 n ^ 2) ≤ b)
    (ho : c ≤ ∑' n : ℕ, normalizedCoefficient β 1 n ^ 2)
    (ho' : (∑' n : ℕ, normalizedCoefficient β 1 n ^ 2) ≤ d) :
    (2 * a - 1) / (2 * d) ≤ (g β 1 / g β 0) ^ 2 ∧
    (g β 1 / g β 0) ^ 2 ≤ (2 * b - 1) / (2 * c) := by
  rw [seed_ratio_sq hβ, seedScale_zero hβ, seedScale_one hβ]
  constructor
  · exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  · exact div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)

end KsIndex.PowerArc
