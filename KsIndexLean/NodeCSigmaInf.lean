module

public import KsIndexLean.NodeCQLowerArith

@[expose] public section


/-!
# Comparison with the limiting Fourier symbol

For `k ≥ 1` and `|ℓ+a| > 0`, the limiting symbol
`σ_{(a;∞)}(ℓ) = ((ℓ+a)² − 1)/|ℓ+a|` is strictly smaller than `σ_{(a;k)}(ℓ)`.
On tail modes where the limiting symbol is positive, this gives the reciprocal
comparison used in the trial-function estimate. Summation of the tail is separate.

This file also identifies `Rs (a(1−a))` with
`1/|σ_∞(0)| + 1/|σ_∞(−1)|` for `0 < a < 1`.
-/

noncomputable section
namespace KsIndex.NodeC

/-- The `k → ∞` limit symbol `σ_{(a;∞)}(ℓ) = ((ℓ+a)² − 1)/|ℓ+a|`. -/
def sigmaInf (a : ℝ) (ℓ : ℤ) : ℝ := (((ℓ : ℝ) + a) ^ 2 - 1) / |(ℓ : ℝ) + a|

/-- `(1 − 1/k)² < 1` for `k ≥ 1`. -/
lemma one_sub_inv_sq_lt_one {k : ℕ} (hk : 1 ≤ k) : (1 - 1 / (k : ℝ)) ^ 2 < 1 := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have h0 : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    rw [sub_nonneg, div_le_one hkR]; exact_mod_cast (show 1 ≤ k by omega)
  have h1 : 1 - 1 / (k : ℝ) < 1 := by
    have : (0 : ℝ) < 1 / (k : ℝ) := by positivity
    linarith
  nlinarith [h0, h1]

/-- **`σ_∞ < σ_k`**: the limit symbol strictly undershoots the paper symbol (`k ≥ 1`). -/
lemma sigmaInf_lt_sigma {k : ℕ} (hk : 1 ≤ k) {a : ℝ} {ℓ : ℤ} (hden : 0 < |(ℓ : ℝ) + a|) :
    sigmaInf a ℓ < sigma k a ℓ := by
  rw [sigmaInf, sigma, div_lt_div_iff_of_pos_right hden]
  have := one_sub_inv_sq_lt_one hk
  linarith

/-! ### `R(a)` from the `σ_∞` values -/

section RConnection
variable {a : ℝ}

lemma sigmaInf_zero (ha0 : 0 < a) : sigmaInf a 0 = (a ^ 2 - 1) / a := by
  rw [sigmaInf, Int.cast_zero, zero_add, abs_of_pos ha0]

lemma sigmaInf_negOne (ha1 : a < 1) : sigmaInf a (-1) = (a ^ 2 - 2 * a) / (1 - a) := by
  have hlt : ((-1 : ℤ) : ℝ) + a < 0 := by push_cast; linarith
  rw [sigmaInf, abs_of_neg hlt]
  have hne : ((-1 : ℤ) : ℝ) + a ≠ 0 := ne_of_lt hlt
  push_cast
  rw [div_eq_div_iff (by push_cast at hlt ⊢; linarith) (by linarith)]
  ring

/-- **`R(a) = 1/|σ_∞(0)| + 1/|σ_∞(−1)|`** on `a ∈ (0,1)`: the closed form `Rs (a(1−a))`
identifies with the reciprocal-sum of the two negative `σ_∞` values. -/
lemma Rs_eq_sigmaInf_recip (ha0 : 0 < a) (ha1 : a < 1) :
    Rs (a * (1 - a)) = 1 / |sigmaInf a 0| + 1 / |sigmaInf a (-1)| := by
  have hsi0 : sigmaInf a 0 = (a ^ 2 - 1) / a := sigmaInf_zero ha0
  have hsi1 : sigmaInf a (-1) = (a ^ 2 - 2 * a) / (1 - a) := sigmaInf_negOne ha1
  have habs0 : |sigmaInf a 0| = (1 - a ^ 2) / a := by
    rw [hsi0, abs_div, abs_of_pos ha0, abs_of_neg (by nlinarith : a ^ 2 - 1 < 0)]
    ring
  have habs1 : |sigmaInf a (-1)| = a * (2 - a) / (1 - a) := by
    rw [hsi1, abs_div, abs_of_pos (by linarith : (0:ℝ) < 1 - a),
      abs_of_neg (by nlinarith : a ^ 2 - 2 * a < 0)]
    ring
  rw [habs0, habs1, Rs]
  have h1a : (0:ℝ) < 1 - a := by linarith
  have h1a2 : (0:ℝ) < 1 + a := by linarith
  have h2a : (0:ℝ) < 2 - a := by linarith
  have hs : (0:ℝ) < a * (1 - a) := by positivity
  have hs2 : (0:ℝ) < a * (1 - a) + 2 := by linarith
  have hden0 : (0:ℝ) < 1 - a ^ 2 := by nlinarith
  field_simp
  ring

end RConnection
end KsIndex.NodeC
