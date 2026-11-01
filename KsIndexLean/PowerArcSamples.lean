module

public import KsIndexLean.PowerArcNormalized

@[expose] public section


/-! Evaluation of power-arc coefficients at integer frequencies. -/

namespace KsIndex.PowerArc

lemma normalized_g_nat {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    g β n / g β 0 = (g β ((n % 2 : ℕ) : ℝ) / g β 0) *
      normalizedCoefficient β ((n % 2 : ℕ) : ℝ) (n / 2) := by
  have hn : (n : ℝ) = (n % 2 : ℕ) + 2 * (n / 2 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 2).symm
  rw [hn, g_eq_normalizedCoefficient hβ (Nat.cast_nonneg _)]
  ring

end KsIndex.PowerArc
