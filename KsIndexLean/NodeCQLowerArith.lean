module

public import KsIndexLean.NodeCSymbol

@[expose] public section


/-!
# Arithmetic inequality for the trial-function lower bound

The `Q`-lower proof reduces, after the `Ψ` Fourier tail bound, to showing
`(4/25)·H(a) + 32/75 < R(a)` for all `a ∈ (0,1)`, equivalently `75·R − 12·H > 32`.  The paper
proves the stronger `75·R − 12·H ≥ 70` in the involution variable `s = a(1−a) ∈ (0, 1/4]`,
where

  `H = 3(s+1)/(s(s+6))`,   `R = (1−s)/(s(s+2))`.

This file proves that closing inequality as a self-contained real fact.  Identification of the `H` and `R` closed forms with the relevant `σ_∞` sums
is separate from these arithmetic statements.
-/

noncomputable section
namespace KsIndex.NodeC

/-- The paper's `H(a)` in the involution variable `s = a(1−a)`. -/
def Hs (s : ℝ) : ℝ := 3 * (s + 1) / (s * (s + 6))

/-- The paper's `R(a)` in the involution variable `s = a(1−a)`. -/
def Rs (s : ℝ) : ℝ := (1 - s) / (s * (s + 2))

/-- **Closing inequality**: `75·R − 12·H ≥ 70` on `s = a(1−a) ∈ (0, 1/4]`
(whence `(4/25)·H + 32/75 < R`, the sufficient condition for `Q`-lower). -/
lemma Rs_Hs_ineq {s : ℝ} (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) :
    70 ≤ 75 * Rs s - 12 * Hs s := by
  have hs2 : (0 : ℝ) < s + 2 := by linarith
  have hs6 : (0 : ℝ) < s + 6 := by linarith
  have hkey : 75 * Rs s - 12 * Hs s - 70
      = -(70 * s ^ 3 + 671 * s ^ 2 + 1323 * s - 378) / (s * (s + 2) * (s + 6)) := by
    rw [Rs, Hs]
    field_simp
    ring
  have hnum : 70 * s ^ 3 + 671 * s ^ 2 + 1323 * s - 378 ≤ 0 := by
    nlinarith [mul_nonneg (mul_nonneg hs0.le hs0.le) (by linarith : (0 : ℝ) ≤ 1 / 4 - s),
      mul_nonneg hs0.le (by linarith : (0 : ℝ) ≤ 1 / 4 - s), hs0.le,
      (by linarith : (0 : ℝ) ≤ 1 / 4 - s)]
  have hpos : 0 ≤ 75 * Rs s - 12 * Hs s - 70 := by
    rw [hkey]
    apply div_nonneg (by linarith) (by positivity)
  linarith

/-- The sufficient condition as stated in the paper: `(4/25)·H + 32/75 < R`. -/
lemma Hs_Rs_sufficient {s : ℝ} (hs0 : 0 < s) (hs4 : s ≤ 1 / 4) :
    (4 / 25) * Hs s + 32 / 75 < Rs s := by
  have := Rs_Hs_ineq hs0 hs4
  linarith

end KsIndex.NodeC
