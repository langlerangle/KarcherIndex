module

/-
# A negative coefficient witness for the single-arc form

The real coefficient model of the `k = 3` single-arc form from [ksindexi] §3 is
`NformArc a u = ∑' ℓ, sigArc a ℓ * u ℓ²`, where
`sigArc a ℓ = ((ℓ + a)² - (2/3)²) / |ℓ + a|`.
The normalization omits the positive factor `2π`, which does not affect signs.

`NformArc_witness_neg` proves that the Catalan coefficient sequence `c` from
`TestField` has strictly negative form value at `a = 2/3`. The proof uses its
weighted-square sum `1/4`, proves summability of the inverse-weighted series,
and bounds that nonnegative series below by its three terms at `0`, `-1`,
and `1`, whose sum is `93/160`.

This theorem supplies a negative witness at the coefficient level. Its
transport to a function space or geometric index statement is separate.
-/
public import KsIndexLean.TestField

@[expose] public section


noncomputable section

namespace KsIndex.SingleArc

open KsIndex.TestField Real Filter Topology

/-- The `k=3` single-arc symbol `σ_{(a;3)}(ℓ) = ((ℓ+a)² − (2/3)²)/|ℓ+a|`. -/
def sigArc (a : ℝ) (ℓ : ℤ) : ℝ := (((ℓ : ℝ) + a) ^ 2 - 4 / 9) / |(ℓ : ℝ) + a|

/-- The single-arc form on a real coefficient sequence. -/
def NformArc (a : ℝ) (u : ℤ → ℝ) : ℝ := ∑' ℓ : ℤ, sigArc a ℓ * u ℓ ^ 2

/-! ### The witness bound at `a = 2/3` -/

lemma habs_ge (ℓ : ℤ) : (1 : ℝ) / 3 ≤ |(ℓ : ℝ) + 2 / 3| := by
  rcases le_or_gt 0 ℓ with h | h
  · have hn : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith
  · have hle : ℓ ≤ -1 := by omega
    have hn : (ℓ : ℝ) ≤ -1 := by exact_mod_cast hle
    rw [abs_of_neg (by linarith)]; linarith

lemma habs_pos (ℓ : ℤ) : 0 < |(ℓ : ℝ) + 2 / 3| :=
  lt_of_lt_of_le (by norm_num) (habs_ge ℓ)

/-- The `c²/|ℓ+2/3|` series is summable (dominated by `9·|ℓ+2/3|·c²`). -/
lemma summable_c_sq_div : Summable (fun ℓ : ℤ => c ℓ ^ 2 / |(ℓ : ℝ) + 2 / 3|) := by
  have hdom : Summable (fun ℓ : ℤ => 9 * (|(ℓ : ℝ) + 2 / 3| * c ℓ ^ 2)) :=
    (summable_abs_mul_sq (show (2 / 3 : ℝ) ∈ Set.Ioo 0 1 by norm_num)).mul_left 9
  refine hdom.of_nonneg_of_le (fun ℓ => by positivity) fun ℓ => ?_
  have hpos := habs_pos ℓ
  have h9 : (1 : ℝ) ≤ 9 * |(ℓ : ℝ) + 2 / 3| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (habs_ge ℓ))
      (by linarith [habs_ge ℓ] : (0 : ℝ) ≤ |(ℓ : ℝ) + 2 / 3| + 1 / 3)]
  rw [div_le_iff₀ hpos]
  nlinarith [h9, sq_nonneg (c ℓ), hpos]

/-- `σ_{(2/3;3)}(ℓ)·c(ℓ)² = |ℓ+2/3|·c(ℓ)² − (4/9)·c(ℓ)²/|ℓ+2/3|`. -/
lemma sigArc_mul (ℓ : ℤ) :
    sigArc (2 / 3) ℓ * c ℓ ^ 2
      = |(ℓ : ℝ) + 2 / 3| * c ℓ ^ 2 - 4 / 9 * (c ℓ ^ 2 / |(ℓ : ℝ) + 2 / 3|) := by
  have hpos := habs_pos ℓ
  rw [sigArc, ← sq_abs ((ℓ : ℝ) + 2 / 3)]
  field_simp

/-- The test sequence `c` has strictly negative single-arc form value at `a = 2/3`. -/
theorem NformArc_witness_neg : NformArc (2 / 3) c < 0 := by
  have ha : (2 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have hsum1 : Summable (fun ℓ : ℤ => |(ℓ : ℝ) + 2 / 3| * c ℓ ^ 2) := summable_abs_mul_sq ha
  have hsum2 := summable_c_sq_div
  -- `NformArc = 1/4 − (4/9)·∑ c²/|ℓ+2/3|`.
  have hsplit : NformArc (2 / 3) c
      = 1 / 4 - 4 / 9 * ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + 2 / 3| := by
    have e : NformArc (2 / 3) c
        = (∑' ℓ : ℤ, |(ℓ : ℝ) + 2 / 3| * c ℓ ^ 2)
          - ∑' ℓ : ℤ, 4 / 9 * (c ℓ ^ 2 / |(ℓ : ℝ) + 2 / 3|) := by
      rw [NformArc, ← hsum1.tsum_sub (hsum2.mul_left (4 / 9))]
      exact tsum_congr fun ℓ => sigArc_mul ℓ
    rw [e, test_field ha, tsum_mul_left]
  -- Lower bound on the tail sum by the `ℓ = 0, -1, 1` terms.
  have hlb : (93 : ℝ) / 160 ≤ ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + 2 / 3| := by
    have hle := hsum2.sum_le_tsum ({0, -1, 1} : Finset ℤ) (fun ℓ _ => by positivity)
    have hcm1 : c (-1) ^ 2 = 1 / 8 := by
      rw [show (-1 : ℤ) = -0 - 1 by ring, c_reflect, c_zero_sq]
    have hval : ∑ ℓ ∈ ({0, -1, 1} : Finset ℤ), c ℓ ^ 2 / |(ℓ : ℝ) + 2 / 3| = 93 / 160 := by
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
        c_zero_sq, hcm1, c_one_sq,
        show |((0 : ℤ) : ℝ) + 2 / 3| = 2 / 3 by norm_num,
        show |((-1 : ℤ) : ℝ) + 2 / 3| = 1 / 3 by norm_num,
        show |((1 : ℤ) : ℝ) + 2 / 3| = 5 / 3 by norm_num]
      norm_num
    rw [hval] at hle; exact hle
  rw [hsplit]; linarith [hlb]

end KsIndex.SingleArc
