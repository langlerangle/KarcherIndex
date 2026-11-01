module

public import KsIndexLean.PowerArcSeedTails

@[expose] public section


/-! Rational recurrences for normalized power-arc coefficients. -/

namespace KsIndex.PowerArc

noncomputable def normalizedCoefficient (β r : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => (β - (r + 2 * n)) / (r + 2 * n + β + 2) *
      normalizedCoefficient β r n

lemma g_eq_normalizedCoefficient {β r : ℝ} (hβ : 0 < β) (hr : 0 ≤ r) (n : ℕ) :
    g β (r + 2 * n) = g β r * normalizedCoefficient β r n := by
  induction n with
  | zero => simp [normalizedCoefficient]
  | succ n ih =>
    have hd : r + 2 * n + β + 2 ≠ 0 := by positivity
    have hh := g_step_two hβ (r + 2 * n)
    rw [ih] at hh
    simp only [normalizedCoefficient, Nat.cast_add, Nat.cast_one]
    rw [show r + 2 * ((n : ℝ) + 1) = (r + 2 * n) + 2 by ring]
    field_simp
    nlinarith [hh]

lemma normalizedCoefficient_eq {β r : ℝ} (hβ : 0 < β) (hr : 0 ≤ r)
    (hg : g β r ≠ 0) (n : ℕ) :
    normalizedCoefficient β r n = g β (r + 2 * n) / g β r := by
  rw [g_eq_normalizedCoefficient hβ hr]
  field_simp

/-- Normalized coefficients have an explicit two-sided tail enclosure.
For rational parameters, all expressions bounding the tail are rational. -/
theorem normalized_tail_bounds {β r : ℝ} (hβ : 0 < β) (hr : 0 ≤ r)
    (hg : g β r ≠ 0) (N : ℕ) (hN : 1 ≤ r + 2 * N)
    (he : squareTailError β (r + 2 * N) < 1) :
    let L := (r + 2 * N + 2 * β + 1) * normalizedCoefficient β r N ^ 2 /
      (2 * (2 * β + 1))
    L ≤ ∑' n : ℕ, normalizedCoefficient β r (N + n) ^ 2 ∧
    (∑' n : ℕ, normalizedCoefficient β r (N + n) ^ 2) ≤
      L / (1 - squareTailError β (r + 2 * N)) := by
  dsimp only
  have hb := square_tail_bounds hβ hN he
  have hsq : 0 < g β r ^ 2 := sq_pos_of_ne_zero hg
  have hterm : ∀ n : ℕ, normalizedCoefficient β r (N + n) ^ 2 =
      g β ((r + 2 * N) + 2 * n) ^ 2 / g β r ^ 2 := by
    intro n
    rw [normalizedCoefficient_eq hβ hr hg, div_pow]
    push_cast
    rw [show r + 2 * ((N : ℝ) + n) = (r + 2 * N) + 2 * n by ring]
  have hsum : (∑' n : ℕ, normalizedCoefficient β r (N + n) ^ 2) =
      (∑' n : ℕ, g β ((r + 2 * N) + 2 * n) ^ 2) / g β r ^ 2 := by
    simp only [hterm, tsum_div_const]
  have hL : squareTailPrimitive β (r + 2 * N) / g β r ^ 2 =
      (r + 2 * N + 2 * β + 1) * normalizedCoefficient β r N ^ 2 /
        (2 * (2 * β + 1)) := by
    rw [squareTailPrimitive, g_eq_normalizedCoefficient hβ hr]
    field_simp
  rw [hsum, ← hL]
  constructor
  · exact div_le_div_of_nonneg_right hb.1 hsq.le
  · simpa only [div_div, mul_comm] using div_le_div_of_nonneg_right hb.2 hsq.le

end KsIndex.PowerArc
