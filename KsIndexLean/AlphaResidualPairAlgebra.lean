module

public import Mathlib

@[expose] public section


/-! Rational identities for paired tails of the circle-form residual.

These identities isolate the constant leading term and retain the dependence
on the residual index. They assert no convergence or numerical spectral sign.
-/

namespace KsIndex.AlphaResidual

/-- Pairing opposite denominators keeps the difference of the weighted
envelopes visible before taking absolute values. -/
theorem paired_fraction_identity (x n p q a b : ℝ)
    (hm : x - 2 * n ≠ 0) (hp : x + 2 * n ≠ 0) :
    p * (a + b) / (x - 2 * n) - q * (a - b) / (x + 2 * n) =
      ((x * (p - q) + 2 * n * (p + q)) * a +
        (x * (p + q) + 2 * n * (p - q)) * b) / (x ^ 2 - 4 * n ^ 2) := by
  have hd : x ^ 2 - 4 * n ^ 2 ≠ 0 := by
    have h := mul_ne_zero hm hp
    convert h using 1
    ring
  rw [show x ^ 2 - 4 * n ^ 2 = (x - 2 * n) * (x + 2 * n) by ring]
  field_simp
  ring

/-- Difference of the two reflected frequency weights. -/
theorem reflected_weight_difference (x : ℝ)
    (hm : 3 * x - 1 ≠ 0) (hp : 3 * x + 1 ≠ 0) :
    (3 * x + 1 - 4 / (3 * x + 1)) -
      (3 * x - 1 - 4 / (3 * x - 1)) = 2 + 8 / (9 * x ^ 2 - 1) := by
  have hd : 9 * x ^ 2 - 1 ≠ 0 := by
    have h := mul_ne_zero hm hp
    convert h using 1
    ring
  rw [show 9 * x ^ 2 - 1 = (3 * x - 1) * (3 * x + 1) by ring]
  field_simp
  ring

/-- Sum of the two reflected frequency weights. -/
theorem reflected_weight_sum (x : ℝ)
    (hm : 3 * x - 1 ≠ 0) (hp : 3 * x + 1 ≠ 0) :
    (3 * x + 1 - 4 / (3 * x + 1)) +
      (3 * x - 1 - 4 / (3 * x - 1)) =
        6 * x - 24 * x / (9 * x ^ 2 - 1) := by
  have hd : 9 * x ^ 2 - 1 ≠ 0 := by
    have h := mul_ne_zero hm hp
    convert h using 1
    ring
  rw [show 9 * x ^ 2 - 1 = (3 * x - 1) * (3 * x + 1) by ring]
  field_simp
  ring

/-- The symmetric-envelope coefficient has an exact constant leading part. -/
theorem paired_leading_extraction (x n : ℝ)
    (hn : x ^ 2 - 4 * n ^ 2 ≠ 0) :
    (x * (6 * x - 24 * x / (9 * x ^ 2 - 1)) +
      2 * n * (2 + 8 / (9 * x ^ 2 - 1))) / (x ^ 2 - 4 * n ^ 2) =
    6 + (24 * n ^ 2 + 4 * n + (16 * n - 24 * x ^ 2) /
      (9 * x ^ 2 - 1)) / (x ^ 2 - 4 * n ^ 2) := by
  apply (div_eq_iff hn).2
  rw [add_mul, div_mul_cancel₀ _ hn]
  ring

/-- The other coefficient retains its index-dependent leading factor. -/
theorem paired_other_coefficient (x n : ℝ) :
    (x * (2 + 8 / (9 * x ^ 2 - 1)) +
      2 * n * (6 * x - 24 * x / (9 * x ^ 2 - 1))) /
        (x ^ 2 - 4 * n ^ 2) =
    x * ((2 + 12 * n) + (8 - 48 * n) / (9 * x ^ 2 - 1)) /
      (x ^ 2 - 4 * n ^ 2) := by
  ring

/-- A partial fraction identity for the signed frequency symbol. -/
theorem signed_symbol_partial_fraction (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : b - a ≠ 0) :
    (b - 4 / b) / (b - a) =
      (a - 4 / a) / (b - a) + 1 + 4 / (a * b) := by
  field_simp
  ring

end KsIndex.AlphaResidual
