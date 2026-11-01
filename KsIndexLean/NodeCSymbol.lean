module

public import KsIndexLean.DtNCircle

@[expose] public section


/-!
# Single-arc Dirichlet-to-Neumann symbol and its sign classification

In the paper's single-arc `(a;k)` coordinate, the symbol is
`σ_{(a;k)}(ℓ) = ((ℓ+a)² − (1−1/k)²)/|ℓ+a|`. This file proves that, for
`a = 1 − j/k` with `k ≥ 4` and `2 ≤ j ≤ k−2` (written `2 ≤ j`, `j + 2 ≤ k`), exactly the two
modes `ℓ ∈ {0, −1}` have `σ(ℓ) < 0`, and every other `ℓ` has `σ(ℓ) > 0`.

For these parameters the denominator is strictly positive at every integer mode.
These scalar sign lemmas are inputs to the quadratic-form estimates and the
two-coefficient argument; neither argument is carried out in this file.
-/

noncomputable section
namespace KsIndex.NodeC

/-- Paper single-arc DtN symbol `σ_{(a;k)}(ℓ) = ((ℓ+a)² − (1−1/k)²)/|ℓ+a|`. -/
def sigma (k : ℕ) (a : ℝ) (ℓ : ℤ) : ℝ :=
  (((ℓ : ℝ) + a) ^ 2 - (1 - 1 / (k : ℝ)) ^ 2) / |(ℓ : ℝ) + a|

/-- For `a ∈ (0,1)`, `ℓ + a` is never an integer, hence never `0`. -/
lemma abs_add_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (ℓ : ℤ) : 0 < |(ℓ : ℝ) + a| := by
  rw [abs_pos]
  intro h
  have h0 : (0 : ℤ) < -ℓ := by
    have : (0 : ℝ) < ((-ℓ : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : (-ℓ : ℤ) < 1 := by
    have : ((-ℓ : ℤ) : ℝ) < 1 := by push_cast; linarith
    exact_mod_cast this
  omega

/-- Sign reduction: positive denominator + `|ℓ+a| < 1−1/k` give `σ < 0`. -/
lemma sigma_neg {k : ℕ} {a : ℝ} {ℓ : ℤ} (hden : 0 < |(ℓ : ℝ) + a|)
    (h : |(ℓ : ℝ) + a| < 1 - 1 / (k : ℝ)) : sigma k a ℓ < 0 := by
  apply div_neg_of_neg_of_pos _ hden
  nlinarith [sq_abs ((ℓ : ℝ) + a), abs_nonneg ((ℓ : ℝ) + a), h]

/-- Sign reduction: positive denominator + `1−1/k < |ℓ+a|` (with `0 ≤ 1−1/k`) give `0 < σ`. -/
lemma sigma_pos {k : ℕ} {a : ℝ} {ℓ : ℤ} (hden : 0 < |(ℓ : ℝ) + a|)
    (hnn : 0 ≤ 1 - 1 / (k : ℝ)) (h : 1 - 1 / (k : ℝ) < |(ℓ : ℝ) + a|) :
    0 < sigma k a ℓ := by
  apply div_pos _ hden
  nlinarith [sq_abs ((ℓ : ℝ) + a), abs_nonneg ((ℓ : ℝ) + a), h, hnn]

/-! ### The census -/

/-- The class angle `a(j,k) = 1 − j/k`. -/
def censusA (j k : ℕ) : ℝ := 1 - (j : ℝ) / (k : ℝ)

section Census
variable {k j : ℕ}

lemma kR_pos (hk : 4 ≤ k) : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)

lemma censusA_pos (hk : 4 ≤ k) (hjk : j + 2 ≤ k) : 0 < censusA j k := by
  rw [censusA, sub_pos, div_lt_one (kR_pos hk)]; exact_mod_cast (show j < k by omega)

lemma censusA_lt_one (hk : 4 ≤ k) (hj2 : 2 ≤ j) : censusA j k < 1 := by
  have : (0 : ℝ) < (j : ℝ) / (k : ℝ) :=
    div_pos (by exact_mod_cast (show 0 < j by omega)) (kR_pos hk)
  rw [censusA]; linarith

lemma onemk_nonneg (hk : 4 ≤ k) : 0 ≤ 1 - 1 / (k : ℝ) := by
  rw [sub_nonneg, div_le_one (kR_pos hk)]; exact_mod_cast (show 1 ≤ k by omega)

lemma onemk_lt_one (hk : 4 ≤ k) : 1 - 1 / (k : ℝ) < 1 := by
  have : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  linarith

/-- `σ(0) < 0` — because `a < 1 − 1/k` (i.e. `j > 1`). -/
lemma sigma_census_zero (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k) :
    sigma k (censusA j k) 0 < 0 := by
  have ha0 := censusA_pos hk hjk
  have ha1 := censusA_lt_one hk hj2
  refine sigma_neg (abs_add_pos ha0 ha1 0) ?_
  rw [Int.cast_zero, zero_add, abs_of_pos ha0, censusA]
  rw [sub_lt_sub_iff_left, div_lt_div_iff_of_pos_right (kR_pos hk)] -- 1/k < j/k ⟺ 1 < j
  · exact_mod_cast (show 1 < j by omega)

/-- `σ(−1) < 0` — because `1 − a = j/k < 1 − 1/k` (i.e. `j < k − 1`). -/
lemma sigma_census_negOne (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k) :
    sigma k (censusA j k) (-1) < 0 := by
  have ha0 := censusA_pos hk hjk
  have ha1 := censusA_lt_one hk hj2
  refine sigma_neg (abs_add_pos ha0 ha1 (-1)) ?_
  have hlt : ((-1 : ℤ) : ℝ) + censusA j k < 0 := by push_cast; linarith
  rw [abs_of_neg hlt]
  have heq : -(((-1 : ℤ) : ℝ) + censusA j k) = (j : ℝ) / (k : ℝ) := by
    push_cast; rw [censusA]; ring
  rw [heq, div_lt_iff₀ (kR_pos hk)]
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt (kR_pos hk)
  have hexp : (1 - 1 / (k : ℝ)) * (k : ℝ) = (k : ℝ) - 1 := by
    rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ hkne]
  rw [hexp]
  have hjk' : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hjk
  linarith

/-- `σ(ℓ) > 0` for every `ℓ ∉ {0, −1}` — because `|ℓ+a| > 1 > 1−1/k`. -/
lemma sigma_census_else (hk : 4 ≤ k) (hj2 : 2 ≤ j) (hjk : j + 2 ≤ k)
    {ℓ : ℤ} (h0 : ℓ ≠ 0) (h1 : ℓ ≠ -1) : 0 < sigma k (censusA j k) ℓ := by
  have ha0 := censusA_pos hk hjk
  have ha1 := censusA_lt_one hk hj2
  refine sigma_pos (abs_add_pos ha0 ha1 ℓ) (onemk_nonneg hk) ?_
  have honemk := onemk_lt_one hk
  rcases (show 1 ≤ ℓ ∨ ℓ ≤ -2 by omega) with hge | hle
  · -- ℓ ≥ 1: ℓ + a ≥ 1 + a > 1 > 1 − 1/k
    have hpos : (0 : ℝ) < (ℓ : ℝ) + censusA j k := by
      have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hge
      linarith
    rw [abs_of_pos hpos]
    have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hge
    linarith
  · -- ℓ ≤ −2: ℓ + a ≤ −2 + a < −1, so |ℓ+a| = −(ℓ+a) ≥ 2 − a > 1 > 1 − 1/k
    have hneg : (ℓ : ℝ) + censusA j k < 0 := by
      have : (ℓ : ℝ) ≤ -2 := by exact_mod_cast hle
      linarith
    rw [abs_of_neg hneg]
    have : (ℓ : ℝ) ≤ -2 := by exact_mod_cast hle
    linarith

end Census
end KsIndex.NodeC
