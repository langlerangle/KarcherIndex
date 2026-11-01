module

/-
KsIndexLean — The explicit arc estimate for the paper's `Q-lower` inequality.

For `a ∈ (0,1)`, `a < b`, `1-a < b` and `|b| ≤ 1`, the theorem `Sconst_lt`
proves that the sum of `psiHat ℓ ^ 2 / sigmaArc a b ℓ` over `ℓ ≠ 0,-1`
is strictly less than `-1/sigmaArc a b 0 - 1/sigmaArc a b (-1)`.
The two distinguished symbols are negative under these hypotheses.

The proof uses the comparison
`sigmaArc a b ℓ ≥ |ℓ+a| - 1/|ℓ+a|`. The terms at `ℓ = 1,-2` are bounded
above using `Hfun a`; away from `-2,-1,0,1`, the symbol is at least `3/2`.
The summable pair-weight majorant then gives
`Sconst a b ≤ (4/(2+π)²)*(Hfun a + π²/3)`.

The reciprocal sum is bounded below by `Rfun a`. Substituting `s = a*(1-a)`
expresses `Hfun a` as `3*(s+1)/(s*(s+6))` and `Rfun a` as
`(1-s)/(s*(s+2))`. A cubic inequality on `0 < s ≤ 1/4` proves
`(4/25)*(Hfun a + 10/3) < Rfun a`. Finally, `π > 3` and `π² < 10`
complete the strict comparison.
-/
public import KsIndexLean.ArcPsi

@[expose] public section


noncomputable section

namespace KsIndex.ArcEstimate

open KsIndex.ArcSpace KsIndex.ArcForm KsIndex.ArcPsi Real

/-! ### `σ_{(a;k)} ≥ σ_{(a;∞)}` -/

/-- `σ_{(a;k)}(ℓ) ≥ |ℓ+a| − 1/|ℓ+a|` when `|b| ≤ 1`. -/
lemma sigmaArc_ge_inf (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) (ℓ : ℤ) :
    |(ℓ : ℝ) + a| - 1 / |(ℓ : ℝ) + a| ≤ sigmaArc a b ℓ := by
  have hpos := abs_add_pos ha ℓ
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [abs_nonneg b, sq_abs b]
  rw [sigmaArc_eq ha]
  have : b ^ 2 / |(ℓ : ℝ) + a| ≤ 1 / |(ℓ : ℝ) + a| :=
    div_le_div_of_nonneg_right hb2 hpos.le
  linarith

/-- Off `{−2,−1,0,1}`: `|ℓ+a| ≥ 2`, hence `σ ≥ 3/2`. -/
lemma sigmaArc_ge_three_halves (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) {ℓ : ℤ}
    (h : ℓ ≠ -2 ∧ ℓ ≠ -1 ∧ ℓ ≠ 0 ∧ ℓ ≠ 1) : 3 / 2 ≤ sigmaArc a b ℓ := by
  obtain ⟨h2, h1, h0, h1'⟩ := h
  have hge : 2 ≤ |(ℓ : ℝ) + a| := by
    rcases le_or_gt 0 ℓ with hl | hl
    · have : (2 : ℝ) ≤ ℓ := by exact_mod_cast (show 2 ≤ ℓ by omega)
      rw [abs_of_pos (by linarith [ha.1])]; linarith [ha.1]
    · have : (ℓ : ℝ) ≤ -3 := by exact_mod_cast (show ℓ ≤ -3 by omega)
      rw [abs_of_neg (by linarith [ha.2])]; linarith [ha.2]
  refine le_trans ?_ (sigmaArc_ge_inf ha hb ℓ)
  have : 1 / |(ℓ : ℝ) + a| ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hge
  linarith

/-! ### The two explicit terms and the closed forms `H`, `R` -/

/-- `H(a) = (a+1)/(a(a+2)) + (2−a)/((1−a)(3−a))`. -/
def Hfun (a : ℝ) : ℝ := (a + 1) / (a * (a + 2)) + (2 - a) / ((1 - a) * (3 - a))

/-- `R(a) = a/(1−a²) + (1−a)/(a(2−a))`. -/
def Rfun (a : ℝ) : ℝ := a / (1 - a ^ 2) + (1 - a) / (a * (2 - a))

lemma Hfun_pos (ha : a ∈ Set.Ioo (0 : ℝ) 1) : 0 < Hfun a := by
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  unfold Hfun
  exact add_pos (div_pos (by linarith) (mul_pos ha0 (by linarith)))
    (div_pos (by linarith) (mul_pos ha1 (by linarith)))

/-- `1/σ_{(a;k)}(1) ≤ (a+1)/(a(a+2))`. -/
lemma inv_sigma_one_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) :
    1 / sigmaArc a b 1 ≤ (a + 1) / (a * (a + 2)) := by
  have h := sigmaArc_ge_inf ha hb 1
  have ha0 := ha.1
  push_cast at h
  rw [abs_of_pos (by linarith)] at h
  have hσ : a * (a + 2) / (a + 1) ≤ sigmaArc a b 1 := by
    refine le_trans (le_of_eq ?_) h
    field_simp
    ring
  have hpos : 0 < a * (a + 2) / (a + 1) := by positivity
  calc 1 / sigmaArc a b 1 ≤ 1 / (a * (a + 2) / (a + 1)) :=
        one_div_le_one_div_of_le hpos hσ
    _ = (a + 1) / (a * (a + 2)) := by rw [one_div_div]

/-- `1/σ_{(a;k)}(−2) ≤ (2−a)/((1−a)(3−a))`. -/
lemma inv_sigma_neg_two_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) :
    1 / sigmaArc a b (-2) ≤ (2 - a) / ((1 - a) * (3 - a)) := by
  have h := sigmaArc_ge_inf ha hb (-2)
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have ha2 : 0 < 2 - a := by linarith
  push_cast at h
  rw [abs_of_neg (by linarith), show -(-2 + a) = 2 - a by ring] at h
  have hσ : (1 - a) * (3 - a) / (2 - a) ≤ sigmaArc a b (-2) := by
    refine le_trans (le_of_eq ?_) h
    have hne : (2 - a) ≠ 0 := ha2.ne'
    field_simp
    ring
  have hpos : 0 < (1 - a) * (3 - a) / (2 - a) := div_pos (mul_pos ha1 (by linarith)) ha2
  calc 1 / sigmaArc a b (-2) ≤ 1 / ((1 - a) * (3 - a) / (2 - a)) :=
        one_div_le_one_div_of_le hpos hσ
    _ = (2 - a) / ((1 - a) * (3 - a)) := by rw [one_div_div]

/-! ### The upper bound on `Sconst` -/

/-- The dominating summand: `(4/(2+π)²)[δ₁ H₀ + δ₋₂ H₁ + (2/3) w(ℓ)]`. -/
def domTerm (a : ℝ) (ℓ : ℤ) : ℝ :=
  4 / (2 + π) ^ 2 * ((if ℓ = 1 then (a + 1) / (a * (a + 2)) else 0)
    + (if ℓ = -2 then (2 - a) / ((1 - a) * (3 - a)) else 0) + 2 / 3 * pairW ℓ)

lemma summable_domTerm (a : ℝ) : Summable (domTerm a) := by
  unfold domTerm
  refine Summable.mul_left _ (Summable.add (Summable.add ?_ ?_) (summable_pairW.mul_left _))
  · exact summable_of_ne_finset_zero (s := {1}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]
  · exact summable_of_ne_finset_zero (s := {-2}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]

lemma tsum_domTerm (a : ℝ) :
    ∑' ℓ : ℤ, domTerm a ℓ = 4 / (2 + π) ^ 2 * (Hfun a + π ^ 2 / 3) := by
  unfold domTerm
  have h1 : Summable fun ℓ : ℤ => (if ℓ = 1 then (a + 1) / (a * (a + 2)) else 0) :=
    summable_of_ne_finset_zero (s := {1}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]
  have h2 : Summable fun ℓ : ℤ => (if ℓ = -2 then (2 - a) / ((1 - a) * (3 - a)) else 0) :=
    summable_of_ne_finset_zero (s := {-2}) fun ℓ hℓ => by
      simp only [Finset.mem_singleton] at hℓ; simp [hℓ]
  rw [tsum_mul_left, (h1.add h2).tsum_add (summable_pairW.mul_left _), h1.tsum_add h2,
    tsum_mul_left, hasSum_pairW.tsum_eq, tsum_ite_eq, tsum_ite_eq, Hfun]
  ring

/-- Termwise domination of the `Sconst` summand. -/
lemma Sconst_term_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) (ℓ : ℤ) :
    (if ℓ = 0 ∨ ℓ = -1 then 0 else psiHat ℓ ^ 2 / sigmaArc a b ℓ) ≤ domTerm a ℓ := by
  have hc : 0 < 4 / (2 + π) ^ 2 := by positivity
  have hw : 0 ≤ pairW ℓ := by unfold pairW; positivity
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hH0 : 0 ≤ (a + 1) / (a * (a + 2)) := by positivity
  have hH1 : 0 ≤ (2 - a) / ((1 - a) * (3 - a)) := by
    have : 0 < 2 - a := by linarith
    have : 0 < 3 - a := by linarith
    positivity
  have hd : 0 ≤ domTerm a ℓ := by
    unfold domTerm
    apply mul_nonneg hc.le
    refine add_nonneg (add_nonneg ?_ ?_) (mul_nonneg (by norm_num) hw)
    · split_ifs <;> first | exact hH0 | exact le_rfl
    · split_ifs <;> first | exact hH1 | exact le_rfl
  by_cases h : ℓ = 0 ∨ ℓ = -1
  · rw [if_pos h]; exact hd
  rw [if_neg h]
  push Not at h
  by_cases h1 : ℓ = 1
  · subst h1
    have hσ := inv_sigma_one_le ha hb
    have hψ : psiHat 1 ^ 2 = 4 / (2 + π) ^ 2 * 1 := by
      have := psiHat_sq_odd 0 (by norm_num)
      simp only [mul_zero, zero_add, Int.cast_zero, one_pow, div_one] at this
      rw [this]
    unfold domTerm
    rw [if_pos rfl, if_neg (by norm_num), hψ, mul_one, div_eq_mul_one_div, mul_add, mul_add,
      mul_zero, add_zero]
    nlinarith [mul_le_mul_of_nonneg_left hσ hc.le, mul_nonneg hc.le hw]
  by_cases h2 : ℓ = -2
  · subst h2
    have hσ := inv_sigma_neg_two_le ha hb
    have hψ : psiHat (-2) ^ 2 = 4 / (2 + π) ^ 2 * 1 := by
      have := psiHat_sq_even (-1) (by norm_num)
      rw [show (2 : ℤ) * -1 = -2 by norm_num] at this
      rw [this]
      norm_num
    unfold domTerm
    rw [if_neg (by norm_num), if_pos rfl, hψ, mul_one, div_eq_mul_one_div, mul_add, mul_add,
      mul_zero, zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hσ hc.le, mul_nonneg hc.le hw]
  -- generic tail: σ ≥ 3/2
  have hσ := sigmaArc_ge_three_halves ha hb ⟨h2, h.2, h.1, h1⟩
  have hψ := psiHat_sq_le ℓ
  have hσpos : 0 < sigmaArc a b ℓ := by linarith
  unfold domTerm
  rw [if_neg h1, if_neg h2, zero_add, zero_add, div_le_iff₀ hσpos]
  have : psiHat ℓ ^ 2 ≤ 4 / (2 + π) ^ 2 * (2 / 3 * pairW ℓ) * (3 / 2) := by
    nlinarith [hψ]
  nlinarith [mul_le_mul_of_nonneg_left hσ
    (by positivity : (0 : ℝ) ≤ 4 / (2 + π) ^ 2 * (2 / 3 * pairW ℓ))]

/-- `Sconst(a,b) ≤ (4/(2+π)²)(H(a) + π²/3)`. -/
theorem Sconst_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) :
    Sconst a b ≤ 4 / (2 + π) ^ 2 * (Hfun a + π ^ 2 / 3) := by
  rw [Sconst, ← tsum_domTerm a]
  exact (summable_Sconst_term ha hb).tsum_le_tsum (Sconst_term_le ha hb) (summable_domTerm a)

/-! ### The lower bound on `1/|σ(0)| + 1/|σ(−1)|` -/

lemma sigma_zero_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) :
    sigmaArc a b 0 = (a ^ 2 - b ^ 2) / a := by
  rw [sigmaArc]; push_cast
  rw [zero_add, abs_of_pos ha.1]

lemma sigma_neg_one_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) (b : ℝ) :
    sigmaArc a b (-1) = ((1 - a) ^ 2 - b ^ 2) / (1 - a) := by
  rw [sigmaArc]; push_cast
  rw [abs_of_neg (by linarith [ha.2])]
  congr 1
  · ring
  · ring

/-- `−1/σ(0) − 1/σ(−1) ≥ R(a)` for `a < b`, `1−a < b`, `|b| ≤ 1`. -/
lemma Rfun_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) (hab : a < b) (hab' : 1 - a < b) :
    Rfun a ≤ -1 / sigmaArc a b 0 + -1 / sigmaArc a b (-1) := by
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [abs_nonneg b, sq_abs b]
  have hba : a ^ 2 < b ^ 2 := by nlinarith
  have hba' : (1 - a) ^ 2 < b ^ 2 := by nlinarith
  rw [sigma_zero_eq ha, sigma_neg_one_eq ha, Rfun]
  have hn0 : a ^ 2 - b ^ 2 ≠ 0 := (sub_neg.mpr hba).ne
  have hn0' : b ^ 2 - a ^ 2 ≠ 0 := (sub_pos.mpr hba).ne'
  have hn1 : (1 - a) ^ 2 - b ^ 2 ≠ 0 := (sub_neg.mpr hba').ne
  have hn1' : b ^ 2 - (1 - a) ^ 2 ≠ 0 := (sub_pos.mpr hba').ne'
  have e0 : -1 / ((a ^ 2 - b ^ 2) / a) = a / (b ^ 2 - a ^ 2) := by
    rw [div_div_eq_mul_div, div_eq_div_iff hn0 hn0']
    ring
  have e1 : -1 / (((1 - a) ^ 2 - b ^ 2) / (1 - a)) = (1 - a) / (b ^ 2 - (1 - a) ^ 2) := by
    rw [div_div_eq_mul_div, div_eq_div_iff hn1 hn1']
    ring
  rw [e0, e1]
  have h0 : a / (1 - a ^ 2) ≤ a / (b ^ 2 - a ^ 2) :=
    div_le_div_of_nonneg_left ha0.le (by linarith) (by linarith)
  have h1 : (1 - a) / (a * (2 - a)) ≤ (1 - a) / (b ^ 2 - (1 - a) ^ 2) := by
    rw [show a * (2 - a) = 1 - (1 - a) ^ 2 by ring]
    exact div_le_div_of_nonneg_left ha1.le (by linarith) (by linarith)
  linarith

/-! ### The closed forms in `s = a(1−a)` and the final inequality -/

lemma Hfun_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    Hfun a = 3 * (a * (1 - a) + 1) / (a * (1 - a) * (a * (1 - a) + 6)) := by
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have h2 : 0 < a + 2 := by linarith
  have h3 : 0 < 3 - a := by linarith
  rw [Hfun]
  field_simp
  ring

lemma Rfun_eq (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    Rfun a = (1 - a * (1 - a)) / (a * (1 - a) * (a * (1 - a) + 2)) := by
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have h2 : 0 < 2 - a := by linarith
  have h3 : 0 < 1 - a ^ 2 := by nlinarith
  have h4 : 0 < 1 + a := by linarith
  rw [Rfun]
  field_simp
  ring

/-- The cubic inequality: `(4/25)(3(s+1)/(s(s+6)) + 10/3) < (1−s)/(s(s+2))` for
`s ∈ (0, 1/4]`. -/
lemma cubic_ineq {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1 / 4) :
    4 / 25 * (3 * (s + 1) / (s * (s + 6)) + 10 / 3) < (1 - s) / (s * (s + 2)) := by
  have h6 : 0 < s + 6 := by linarith
  have h2 : 0 < s + 2 := by linarith
  rw [← sub_pos]
  have key : (1 - s) / (s * (s + 2)) - 4 / 25 * (3 * (s + 1) / (s * (s + 6)) + 10 / 3)
      = (378 - 963 * s - 431 * s ^ 2 - 40 * s ^ 3) / (75 * (s * (s + 2) * (s + 6))) := by
    field_simp
    ring
  rw [key]
  apply div_pos _ (by positivity)
  have hs2 : s ^ 2 ≤ s / 4 := by nlinarith
  have hs3 : s ^ 3 ≤ s / 16 := by nlinarith
  nlinarith

/-- `(4/25)(H(a) + 10/3) < R(a)` on `(0,1)`. -/
lemma H_lt_R (ha : a ∈ Set.Ioo (0 : ℝ) 1) : 4 / 25 * (Hfun a + 10 / 3) < Rfun a := by
  rw [Hfun_eq ha, Rfun_eq ha]
  have hs0 : 0 < a * (1 - a) := mul_pos ha.1 (by linarith [ha.2])
  have hs1 : a * (1 - a) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * a - 1)]
  exact cubic_ineq hs0 hs1

/-- **The estimate**: `Sconst(a,b) < 1/|σ(0)| + 1/|σ(−1)|` for the interior classes. -/
theorem Sconst_lt (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) (hab : a < b) (hab' : 1 - a < b) :
    Sconst a b < -1 / sigmaArc a b 0 + -1 / sigmaArc a b (-1) := by
  have h1 := Sconst_le ha hb
  have h2 := H_lt_R ha
  have h3 := Rfun_le ha hb hab hab'
  have hH := Hfun_pos ha
  -- `4/(2+π)² < 4/25` and `π² < 10`
  have hπ : 3 < π := by linarith [pi_gt_three]
  have hπ2 : π ^ 2 < 10 := by nlinarith [pi_lt_d2]
  have hc : 4 / (2 + π) ^ 2 < 4 / 25 := by
    rw [div_lt_div_iff_of_pos_left (by norm_num) (by positivity) (by norm_num)]
    nlinarith
  have h4 : 4 / (2 + π) ^ 2 * (Hfun a + π ^ 2 / 3) < 4 / 25 * (Hfun a + 10 / 3) := by
    have hpos : 0 < Hfun a + π ^ 2 / 3 := by positivity
    calc 4 / (2 + π) ^ 2 * (Hfun a + π ^ 2 / 3) < 4 / 25 * (Hfun a + π ^ 2 / 3) :=
          mul_lt_mul_of_pos_right hc hpos
      _ < 4 / 25 * (Hfun a + 10 / 3) := by
          apply mul_lt_mul_of_pos_left _ (by norm_num)
          linarith
  linarith

end KsIndex.ArcEstimate
