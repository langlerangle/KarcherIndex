module

/-
KsIndexLean — ArcLower: the m=2 lower bound for every class, at the circle level.

For `k ≥ 3` and `1 ≤ j ≤ k−1`, set `a = 1 − j/k` and `b = 1 − 1/k`.
The circle-level result corresponding to [ksindexi] `lower-bound` is
`ind_DN(N_{(a;k)}) ≥ 1`.

More generally, for `0 < a < 1` and any real `b` with `b² ≥ 2a(1−a)`, the
Catalan coefficient sequence `cC` is an arc-supported negative witness. Its form value is

  `NQformArc a b cC = 1/4 − b² ∑ c(ℓ)²/|ℓ+a| < 1/4 − b²/(8a(1−a)) ≤ 0`.

The strict inequality retains the positive `ℓ = 1` term, `c(1)² = 1/32`, in addition
to the two terms at `0` and `−1`. For the class parameters, the required inequality
reduces to `(k−1)² ≥ 2j(k−j)`. The proof treats `k = 3`, where equality holds for
both allowed classes, separately from `k ≥ 4`. Strict negativity still holds when
the parameter inequality is an equality. Arc support is supplied by
`ArcSpace.cC_mem_ArcDom`; this module proves the circle index lower bound, not a
geometric identification with a surface index.
-/
public import KsIndexLean.ArcForm
public import KsIndexLean.FormIndexExt

@[expose] public section


noncomputable section

namespace KsIndex.ArcLower

open KsIndex.ArcSpace KsIndex.ArcForm KsIndex.TestField KsIndex.FormIndex Real

/-- `∑ c(ℓ)²/|ℓ+a|` is summable for `a ∈ (0,1)`. -/
lemma summable_c_sq_div (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    Summable (fun ℓ : ℤ => c ℓ ^ 2 / |(ℓ : ℝ) + a|) := by
  have hm : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  have hdom : Summable (fun ℓ : ℤ => (1 / min a (1 - a) ^ 2) * (|(ℓ : ℝ) + a| * c ℓ ^ 2)) :=
    (summable_abs_mul_sq ha).mul_left _
  refine hdom.of_nonneg_of_le (fun ℓ => by positivity) fun ℓ => ?_
  have hpos := abs_add_pos ha ℓ
  have hge := abs_add_ge ha ℓ
  rw [div_le_iff₀ hpos]
  have h1 : min a (1 - a) ^ 2 ≤ |(ℓ : ℝ) + a| ^ 2 := by nlinarith
  have h2 : c ℓ ^ 2 * min a (1 - a) ^ 2 ≤ c ℓ ^ 2 * |(ℓ : ℝ) + a| ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  have hm2 : 0 < min a (1 - a) ^ 2 := by positivity
  calc c ℓ ^ 2 = (c ℓ ^ 2 * min a (1 - a) ^ 2) / min a (1 - a) ^ 2 := by field_simp
    _ ≤ (c ℓ ^ 2 * |(ℓ : ℝ) + a| ^ 2) / min a (1 - a) ^ 2 :=
        div_le_div_of_nonneg_right h2 hm2.le
    _ = 1 / min a (1 - a) ^ 2 * (|(ℓ : ℝ) + a| * c ℓ ^ 2) * |(ℓ : ℝ) + a| := by ring

/-- The three-term lower bound `∑ c²/|ℓ+a| > c(0)²/a + c(−1)²/(1−a) = 1/(8a(1−a))`
(the `ℓ = 1` term `c(1)²/(1+a) > 0` is dropped). -/
lemma tsum_c_sq_div_gt (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    1 / (8 * (a * (1 - a))) < ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + a| := by
  have hs := summable_c_sq_div ha
  have hF : ∑ ℓ ∈ ({0, -1, 1} : Finset ℤ), c ℓ ^ 2 / |(ℓ : ℝ) + a|
      ≤ ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + a| :=
    hs.sum_le_tsum _ (fun ℓ _ => by positivity)
  refine lt_of_lt_of_le ?_ hF
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num), Finset.sum_singleton]
  have hc1 : c (-1) ^ 2 = 1 / 8 := by
    rw [show (-1 : ℤ) = -0 - 1 by norm_num, c_reflect, c_zero_sq]
  rw [c_zero_sq, hc1, c_one_sq]
  push_cast
  rw [zero_add, abs_of_pos ha.1, abs_of_neg (by linarith [ha.2]), abs_of_pos (by linarith [ha.1])]
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hp : 0 < 1 + a := by linarith
  rw [show -1 + a = -(1 - a) by ring, div_neg, div_neg]
  have key : 1 / (8 * (a * (1 - a))) = 1 / 8 / a + 1 / 8 / (1 - a) := by
    field_simp
    ring
  rw [key]
  have : 0 < 1 / 32 / (1 + a) := by positivity
  linarith

/-- `N_{(a;k)}(c) = 1/4 − b² ∑ c²/|ℓ+a|` (paper's `lower-bound` computation, using
`test_field`). -/
lemma NQformArc_cC_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) :
    NQformArc a b cC = 1 / 4 - b ^ 2 * ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + a| := by
  have hsum1 := summable_abs_mul_sq ha
  have hsum2 := (summable_c_sq_div ha).mul_left (b ^ 2)
  rw [NQformArc, ← test_field ha, ← tsum_mul_left, ← hsum1.tsum_sub hsum2]
  refine tsum_congr fun ℓ => ?_
  rw [cC_apply, KsIndex.GammaOne.norm_ofReal_sq, sigmaArc_eq ha]
  have hpos := abs_add_pos ha ℓ
  field_simp

/-- **The witness is negative** whenever `b² ≥ 2a(1−a)`. -/
theorem NQformArc_cC_neg (ha : a ∈ Set.Ioo (0 : ℝ) 1) {b : ℝ} (hb : 2 * (a * (1 - a)) ≤ b ^ 2) :
    NQformArc a b cC < 0 := by
  rw [NQformArc_cC_eq ha b]
  have h := tsum_c_sq_div_gt ha
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hprod : 0 < a * (1 - a) := mul_pos ha0 ha1
  have hb0 : 0 < b ^ 2 := lt_of_lt_of_le (by positivity) hb
  have h1 : b ^ 2 * (1 / (8 * (a * (1 - a)))) ≤ b ^ 2 * ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + a| :=
    mul_le_mul_of_nonneg_left h.le hb0.le
  have h1' : b ^ 2 * (1 / (8 * (a * (1 - a)))) < b ^ 2 * ∑' ℓ : ℤ, c ℓ ^ 2 / |(ℓ : ℝ) + a| :=
    mul_lt_mul_of_pos_left h hb0
  have h2 : 1 / 4 ≤ b ^ 2 * (1 / (8 * (a * (1 - a)))) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- The integer form of the inequality `b² ≥ 2a(1−a)`: `(k−1)² ≥ 2j(k−j)` for
`k ≥ 3`, `1 ≤ j ≤ k−1`. -/
lemma key_ineq {j k : ℕ} (hk : 3 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) :
    2 * (j : ℝ) * (k - j) ≤ ((k : ℝ) - 1) ^ 2 := by
  have hjk' : j + 1 ≤ k := by omega
  have hjr : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk'
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hj1r : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  -- `(k−1)² − 2j(k−j) = ½(2j−k)² + ½(k(k−4)+2)`: positive for `k ≥ 4`; at `k = 3`
  -- it vanishes exactly at the integers `j ∈ {1,2}` (integrality is essential).
  rcases Nat.lt_or_ge k 4 with h4 | h4
  · have hk3 : k = 3 := by omega
    subst hk3
    have : j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl <;> norm_num
  · have hkr4 : (4 : ℝ) ≤ k := by exact_mod_cast h4
    nlinarith [sq_nonneg (2 * (j : ℝ) - k),
      mul_nonneg (by linarith : (0 : ℝ) ≤ k - 4) (by linarith : (0 : ℝ) ≤ k)]

/-- The parameters of class `(j;k)`: `a = 1 − j/k`, `b = 1 − 1/k`. -/
def aOf (j k : ℕ) : ℝ := 1 - (j : ℝ) / k
def bOf (k : ℕ) : ℝ := 1 - 1 / (k : ℝ)

lemma aOf_mem (hk : 3 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) : aOf j k ∈ Set.Ioo (0 : ℝ) 1 := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hjr : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j + 1 ≤ k by omega)
  have hj1r : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hkpos : (0 : ℝ) < k := by linarith
  constructor
  · rw [aOf, sub_pos, div_lt_one hkpos]; linarith
  · rw [aOf, sub_lt_self_iff]; positivity

lemma bOf_abs_lt (hk : 3 ≤ k) : |bOf k| < 1 := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have h1 : 1 / (k : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hkpos (by norm_num)]; linarith
  have h2 : 0 < 1 / (k : ℝ) := by positivity
  rw [bOf, abs_lt]
  constructor <;> linarith

lemma two_mul_aOf_le (hk : 3 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) :
    2 * (aOf j k * (1 - aOf j k)) ≤ bOf k ^ 2 := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have key := key_ineq hk hj1 hjk
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  rw [aOf, bOf]
  have e1 : 2 * ((1 - (j : ℝ) / k) * (1 - (1 - (j : ℝ) / k))) = 2 * j * (k - j) / (k : ℝ) ^ 2 := by
    field_simp
    ring
  have e2 : (1 - 1 / (k : ℝ)) ^ 2 = ((k : ℝ) - 1) ^ 2 / (k : ℝ) ^ 2 := by
    field_simp
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key hk2.le

/-- **[ksindexi] `lower-bound`, circle level**: `ind_DN(N_{(a;k)}) ≥ 1` for every
`k ≥ 3`, `1 ≤ j ≤ k−1`. -/
theorem one_le_indArc (hk : 3 ≤ k) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1) :
    1 ≤ indArc (aOf j k) (bOf k) :=
  one_le_formIndex_of_neg (NQformArc_smul _ _) cC_mem_ArcDom
    (NQformArc_cC_neg (aOf_mem hk hj1 hjk) (two_mul_aOf_le hk hj1 hjk))

end KsIndex.ArcLower
