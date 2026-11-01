module

/-
Coefficient estimates for the paper's `Q-lower` argument.

For `0 < a < 1`, `Sconst a b` sums the weighted squared coefficients `psiHat`
outside the two frequencies `0` and `−1`. Comparison with `b = 1` reduces its
upper bound to two explicit terms at `1` and `−2`, expressed by `Hfun a`, and
`tailInfTerm`, which omits all four frequencies `−2, −1, 0, 1`. A cubic majorant
and strict integral comparison give

  `∑' l, tailInfTerm a l < 32 / (3 * (2 + π)^2)`.

The resulting bound for `Sconst` allows `|b| ≤ 1`. With the additional interior
conditions `a < b` and `1 − a < b`, the rational estimates yield
`Sconst a b < −1/σ(0) − 1/σ(−1)`. Separate strict comparisons with the limiting
symbol assume `|b| < 1`; the main bound does not require those strict comparisons.

`Q_lower_coeff` also assumes `|b| < 1`, arc support, and distinct coefficients at
`0` and `−1`. It states the coefficient inequality after division by `2π`;
the physical trace/form correspondence is separate. The proof uses exact series
and rational inequalities. `ArcEstimate.Sconst_lt` provides an alternative bound.
-/
public import KsIndexLean.ArcTailIntegral
public import KsIndexLean.ArcRationalFaithful

@[expose] public section


noncomputable section

namespace KsIndex.ArcEstimateFaithful

open KsIndex.ArcSpace KsIndex.ArcForm KsIndex.ArcPsi KsIndex.ArcEstimate
open KsIndex.ArcTailIntegral Real

/-- Positivity of the limiting symbol outside its two negative heads. -/
lemma sigma_inf_pos (ha : a ∈ Set.Ioo (0 : ℝ) 1) {l : ℤ}
    (h0 : l ≠ 0) (h1 : l ≠ -1) : 0 < sigmaArc a 1 l :=
  lt_of_lt_of_le (lt_min ha.1 (by linarith [ha.2]))
    (sigmaArc_tail_ge ha (by norm_num) h0 h1)

lemma tail_geometry (ha : a ∈ Set.Ioo (0 : ℝ) 1) {l : ℤ}
    (h : l ≠ -2 ∧ l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1) :
    2 ≤ |(l : ℝ) + a| ∧ 0 < |(l : ℝ)| - 1 ∧
      |(l : ℝ)| - 1 ≤ |(l : ℝ) + a| := by
  rcases le_or_gt 0 l with hl | hl
  · have hl' : (2 : ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ (l : ℝ)),
      abs_of_pos (by linarith [ha.1] : 0 < (l : ℝ) + a)]
    exact ⟨by linarith [ha.1], by linarith, by linarith [ha.1]⟩
  · have hl' : (l : ℝ) ≤ -3 := by exact_mod_cast (show l ≤ -3 by omega)
    rw [abs_of_neg (by linarith : (l : ℝ) < 0),
      abs_of_neg (by linarith [ha.2] : (l : ℝ) + a < 0)]
    exact ⟨by linarith [ha.2], by linarith, by linarith [ha.2]⟩

lemma sigma_inf_ge_three_quarters (ha : a ∈ Set.Ioo (0 : ℝ) 1) {l : ℤ}
    (h : l ≠ -2 ∧ l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1) :
    3 / 4 * |(l : ℝ) + a| ≤ sigmaArc a 1 l := by
  have hx := (tail_geometry ha h).1
  have hp := abs_add_pos ha l
  rw [sigmaArc_eq ha]
  norm_num only [one_pow]
  have hi : 1 / |(l : ℝ) + a| ≤ |(l : ℝ) + a| / 4 := by
    rw [div_le_iff₀ hp]
    nlinarith
  linarith

/-- The paper's coefficient decay, from parity formulas and no evaluated Basel sum. -/
lemma psiHat_sq_le_cube_weight {l : ℤ} (hl : 0 < |(l : ℝ)| - 1) :
    psiHat l ^ 2 ≤ (4 / (2 + π) ^ 2) / (|(l : ℝ)| - 1) ^ 2 := by
  have hc : 0 ≤ 4 / (2 + π) ^ 2 := by positivity
  have hp : pairW l ≤ 1 / (|(l : ℝ)| - 1) ^ 2 := by
    rcases Int.even_or_odd l with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [← two_mul, pairW_even]
      push_cast at hl ⊢
      rw [← two_mul] at hl
      have habs : |2 * (j : ℝ)| - 1 ≤ |2 * (j : ℝ) + 1| := by
        have hh := abs_add_le (2 * (j : ℝ) + 1) (-1)
        rw [abs_neg, abs_one] at hh
        have he : 2 * (j : ℝ) + 1 + -1 = 2 * (j : ℝ) := by ring
        rw [he] at hh
        linarith
      apply one_div_le_one_div_of_le (sq_pos_of_pos hl)
      nlinarith [sq_abs (2 * (j : ℝ) + 1), abs_nonneg (2 * (j : ℝ) + 1)]
    · rw [pairW_odd]
      push_cast at hl ⊢
      apply one_div_le_one_div_of_le (sq_pos_of_pos hl)
      nlinarith [sq_abs (2 * (j : ℝ) + 1), abs_nonneg (2 * (j : ℝ) + 1)]
  calc psiHat l ^ 2 ≤ 4 / (2 + π) ^ 2 * pairW l := psiHat_sq_le l
    _ ≤ (4 / (2 + π) ^ 2) / (|(l : ℝ)| - 1) ^ 2 := by
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hp hc

/-- The first pointwise comparison in the paper's tail estimate. -/
lemma tail_step_one (ha : a ∈ Set.Ioo (0 : ℝ) 1) {l : ℤ}
    (h : l ≠ -2 ∧ l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1) :
    psiHat l ^ 2 / sigmaArc a 1 l ≤ 4 * psiHat l ^ 2 / (3 * |(l : ℝ) + a|) := by
  have hx := abs_add_pos ha l
  have hs := sigma_inf_ge_three_quarters ha h
  calc psiHat l ^ 2 / sigmaArc a 1 l ≤ psiHat l ^ 2 / (3 / 4 * |(l : ℝ) + a|) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hs
    _ = _ := by ring

/-- Replace the shifted absolute frequency by its lower bound. -/
lemma tail_step_two (ha : a ∈ Set.Ioo (0 : ℝ) 1) {l : ℤ}
    (h : l ≠ -2 ∧ l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1) :
    4 * psiHat l ^ 2 / (3 * |(l : ℝ) + a|) ≤
      4 * psiHat l ^ 2 / (3 * (|(l : ℝ)| - 1)) := by
  obtain ⟨_, hp, hle⟩ := tail_geometry ha h
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- The final cubic pointwise majorant in the paper. -/
lemma tail_step_three {l : ℤ} (hl : 0 < |(l : ℝ)| - 1) :
    4 * psiHat l ^ 2 / (3 * (|(l : ℝ)| - 1)) ≤
      16 / (3 * (2 + π) ^ 2) * cube (|(l : ℝ)| - 1) := by
  have h := psiHat_sq_le_cube_weight hl
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 4))
    (show 0 ≤ 3 * (|(l : ℝ)| - 1) by positivity)
  calc _ ≤ 4 * ((4 / (2 + π) ^ 2) / (|(l : ℝ)| - 1) ^ 2) /
      (3 * (|(l : ℝ)| - 1)) := hm
    _ = _ := by unfold cube; field_simp; ring

open Classical in
/-- The limiting summand with the four exceptional frequencies removed. -/
def tailInfTerm (a : ℝ) (l : ℤ) : ℝ :=
  if l = -2 ∨ l = -1 ∨ l = 0 ∨ l = 1 then 0 else psiHat l ^ 2 / sigmaArc a 1 l

lemma tailInfTerm_nonneg (ha : a ∈ Set.Ioo (0 : ℝ) 1) (l : ℤ) :
    0 ≤ tailInfTerm a l := by
  unfold tailInfTerm
  split_ifs with h
  · exact le_rfl
  · have hn : l ≠ -2 ∧ l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1 := by tauto
    exact div_nonneg (sq_nonneg _) (sigma_inf_pos ha hn.2.2.1 hn.2.1).le

lemma tailInfTerm_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (l : ℤ) :
    tailInfTerm a l ≤ 16 / (3 * (2 + π) ^ 2) * cubeTerm l := by
  unfold tailInfTerm cubeTerm
  split_ifs with h
  · simp
  · have hn : l ≠ -2 ∧ l ≠ -1 ∧ l ≠ 0 ∧ l ≠ 1 := by tauto
    exact (tail_step_one ha hn).trans ((tail_step_two ha hn).trans
      (tail_step_three (tail_geometry ha hn).2.1))

lemma summable_tailInfTerm (ha : a ∈ Set.Ioo (0 : ℝ) 1) : Summable (tailInfTerm a) :=
  (summable_cubeTerm.mul_left _).of_nonneg_of_le (tailInfTerm_nonneg ha) (tailInfTerm_le ha)

/-- The exact constant displayed in the paper, from its cubic integral comparison. -/
theorem tailInf_lt (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    (∑' l : ℤ, tailInfTerm a l) < 32 / (3 * (2 + π) ^ 2) := by
  have hle := (summable_tailInfTerm ha).tsum_le_tsum (tailInfTerm_le ha)
    (summable_cubeTerm.mul_left (16 / (3 * (2 + π) ^ 2)))
  rw [tsum_mul_left] at hle
  have hlt := mul_lt_mul_of_pos_left tsum_cubeTerm_lt_two
    (show 0 < 16 / (3 * (2 + π) ^ 2) by positivity)
  calc _ ≤ _ := hle
    _ < _ := hlt
    _ = _ := by ring

lemma psiHat_sq_one : psiHat 1 ^ 2 = 4 / (2 + π) ^ 2 := by
  simpa using psiHat_sq_odd 0 (by norm_num)

lemma psiHat_sq_neg_two : psiHat (-2) ^ 2 = 4 / (2 + π) ^ 2 := by
  have h := psiHat_sq_even (-1) (by norm_num)
  norm_num at h
  exact h

lemma head_one_exact (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    psiHat 1 ^ 2 / sigmaArc a 1 1 =
      4 / (2 + π) ^ 2 * ((a + 1) / (a * (a + 2))) := by
  have ha0 := ha.1
  have ha1 : 0 < 1 + a := by linarith
  have ha2 : 0 < a + 2 := by linarith
  rw [psiHat_sq_one, sigmaArc]
  norm_num only [Int.cast_one, one_pow]
  rw [abs_of_pos ha1]
  have he : (1 + a) ^ 2 - 1 = a * (a + 2) := by ring
  rw [he]
  field_simp
  ring

lemma head_neg_two_exact (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    psiHat (-2) ^ 2 / sigmaArc a 1 (-2) =
      4 / (2 + π) ^ 2 * ((2 - a) / ((1 - a) * (3 - a))) := by
  have h1 : 0 < 1 - a := by linarith [ha.2]
  have h2 : 0 < 2 - a := by linarith
  have h3 : 0 < 3 - a := by linarith
  rw [psiHat_sq_neg_two, sigmaArc]
  norm_num only [Int.cast_neg, Int.cast_ofNat, one_pow]
  rw [abs_of_neg (by linarith : -2 + a < 0)]
  have he : (-2 + a) ^ 2 - 1 = (1 - a) * (3 - a) := by ring
  rw [he]
  field_simp
  ring

/-- Extract exactly the two frequencies 1 and -2 before estimating the remaining tail. -/
theorem Sconst_inf_split (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    Sconst a 1 = 4 / (2 + π) ^ 2 * Hfun a + ∑' l : ℤ, tailInfTerm a l := by
  classical
  let f : ℤ → ℝ := fun l => if l = 1 then psiHat 1 ^ 2 / sigmaArc a 1 1 else 0
  let g : ℤ → ℝ := fun l => if l = -2 then psiHat (-2) ^ 2 / sigmaArc a 1 (-2) else 0
  have hf : Summable f := summable_of_ne_finset_zero (s := {1}) (by
    intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [f, hl])
  have hg : Summable g := summable_of_ne_finset_zero (s := {-2}) (by
    intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [g, hl])
  have he (l : ℤ) : (if l = 0 ∨ l = -1 then 0 else psiHat l ^ 2 / sigmaArc a 1 l) =
      (f l + g l) + tailInfTerm a l := by
    by_cases h0 : l = 0 <;> by_cases h1 : l = -1 <;>
      by_cases h2 : l = -2 <;> by_cases h3 : l = 1 <;>
      simp_all [f, g, tailInfTerm]
  rw [Sconst, tsum_congr he, (hf.add hg).tsum_add (summable_tailInfTerm ha), hf.tsum_add hg]
  simp only [f, g, tsum_ite_eq]
  rw [head_one_exact ha, head_neg_two_exact ha, Hfun]
  ring

lemma sigma_inf_le (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) (l : ℤ) :
    sigmaArc a 1 l ≤ sigmaArc a b l := by
  simpa only [sigmaArc_eq ha, one_pow] using sigmaArc_ge_inf ha hb l

lemma sigma_inf_lt (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) (l : ℤ) :
    sigmaArc a 1 l < sigmaArc a b l := by
  have hp := abs_add_pos ha l
  have hb2 : b ^ 2 < 1 := by nlinarith [sq_abs b, abs_nonneg b]
  rw [sigmaArc_eq ha, sigmaArc_eq ha]
  norm_num only [one_pow]
  have := div_lt_div_of_pos_right hb2 hp
  linarith

lemma Sconst_term_le_inf (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) (l : ℤ) :
    (if l = 0 ∨ l = -1 then 0 else psiHat l ^ 2 / sigmaArc a b l) ≤
      (if l = 0 ∨ l = -1 then 0 else psiHat l ^ 2 / sigmaArc a 1 l) := by
  split_ifs with h
  · exact le_rfl
  · push Not at h
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sigma_inf_pos ha h.1 h.2)
      (sigma_inf_le ha hb l)

lemma Sconst_le_inf (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) :
    Sconst a b ≤ Sconst a 1 :=
  (summable_Sconst_term ha hb).tsum_le_tsum (Sconst_term_le_inf ha hb)
    (summable_Sconst_term ha (by norm_num))

/-- The strict finite-k comparison from the paper; the limiting case b=1 is separate. -/
lemma Sconst_lt_inf (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) :
    Sconst a b < Sconst a 1 := by
  have hstrict : (if (1 : ℤ) = 0 ∨ (1 : ℤ) = -1 then 0
      else psiHat 1 ^ 2 / sigmaArc a b 1) <
      (if (1 : ℤ) = 0 ∨ (1 : ℤ) = -1 then 0 else psiHat 1 ^ 2 / sigmaArc a 1 1) := by
    norm_num only [Int.reduceEq, or_self, if_false]
    apply div_lt_div_of_pos_left
    · rw [psiHat_sq_one]; positivity
    · exact sigma_inf_pos ha (by norm_num) (by norm_num)
    · exact sigma_inf_lt ha hb 1
  exact Summable.tsum_lt_tsum (Sconst_term_le_inf ha hb.le) hstrict
    (summable_Sconst_term ha hb.le) (summable_Sconst_term ha (by norm_num))

/-- The paper's numerical tail bound, slightly generalized to allow |b|=1. -/
theorem Sconst_lt_paper_bound (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1) :
    Sconst a b < 4 * Hfun a / (2 + π) ^ 2 + 32 / (3 * (2 + π) ^ 2) := by
  have h1 := Sconst_le_inf ha hb
  rw [Sconst_inf_split ha] at h1
  have h2 := tailInf_lt ha
  calc Sconst a b ≤ 4 / (2 + π) ^ 2 * Hfun a + ∑' l : ℤ, tailInfTerm a l := h1
    _ < 4 / (2 + π) ^ 2 * Hfun a + 32 / (3 * (2 + π) ^ 2) :=
      add_lt_add_right h2 _
    _ = _ := by ring

lemma paper_bound_lt_rational (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    4 * Hfun a / (2 + π) ^ 2 + 32 / (3 * (2 + π) ^ 2) <
      4 * Hfun a / 25 + 32 / 75 := by
  have hH := Hfun_pos ha
  have hd : 25 < (2 + π) ^ 2 := by nlinarith [pi_gt_three]
  have hp : 0 < (2 + π) ^ 2 := by positivity
  have h1 := div_lt_div_of_pos_left (show 0 < 4 * Hfun a by positivity) (by norm_num) hd
  have h2 := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 32)
    (by norm_num : (0 : ℝ) < 75) (show 75 < 3 * (2 + π) ^ 2 by linarith)
  linarith

/-- The paper's cubic-tail / R-H proof, retaining ArcEstimate.Sconst_lt as an alternative.
For a finite k, the paper uses b=1-1/k and interior a=1-j/k. -/
theorem Sconst_lt_paper (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| ≤ 1)
    (hab : a < b) (hab' : 1 - a < b) :
    Sconst a b < -1 / sigmaArc a b 0 + -1 / sigmaArc a b (-1) :=
  ((Sconst_lt_paper_bound ha hb).trans (paper_bound_lt_rational ha)).trans_le
    ((KsIndex.ArcRationalFaithful.H_bound_lt_R ha).le.trans (Rfun_le ha hb hab hab'))

/-- The strict negative-head comparison displayed for finite k in the paper. -/
lemma Rfun_lt_strict (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1) (hab : a < b) (hab' : 1 - a < b) :
    Rfun a < -1 / sigmaArc a b 0 + -1 / sigmaArc a b (-1) := by
  have ha0 := ha.1
  have ha1 : 0 < 1 - a := by linarith [ha.2]
  have hb2 : b ^ 2 < 1 := by nlinarith [abs_nonneg b, sq_abs b]
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
  have h0 : a / (1 - a ^ 2) < a / (b ^ 2 - a ^ 2) :=
    div_lt_div_of_pos_left ha0 (by linarith) (by linarith)
  have h1 : (1 - a) / (a * (2 - a)) < (1 - a) / (b ^ 2 - (1 - a) ^ 2) := by
    rw [show a * (2 - a) = 1 - (1 - a) ^ 2 by ring]
    exact div_lt_div_of_pos_left ha1 (by linarith) (by linarith)
  linarith

/-- Coefficient-level Q-lower: the paper's inequality after division by 2*pi.
The physical trace/form correspondence is not supplied by this numerical lemma. -/
theorem Q_lower_coeff (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hb : |b| < 1)
    (hab : a < b) (hab' : 1 - a < b) {u : ℤ → ℂ} (hu : u ∈ ArcDom)
    (hne : u 0 ≠ u (-1)) :
    ‖u 0 - u (-1)‖ ^ 2 *
      ((-sigmaArc a b 0) * (-sigmaArc a b (-1)) /
        ((-sigmaArc a b 0) + (-sigmaArc a b (-1)))) <
      ∑' l : ℤ, tailTerm a b u l := by
  have hs0 : sigmaArc a b 0 < 0 := by
    rw [sigma_zero_eq ha]
    apply div_neg_of_neg_of_pos _ ha.1
    nlinarith [ha.1]
  have hs1 : sigmaArc a b (-1) < 0 := by
    rw [sigma_neg_one_eq ha]
    apply div_neg_of_neg_of_pos _ (by linarith [ha.2])
    nlinarith [ha.2]
  set A := -sigmaArc a b 0
  set B := -sigmaArc a b (-1)
  have hA : 0 < A := neg_pos.mpr hs0
  have hB : 0 < B := neg_pos.mpr hs1
  have hX : 0 < 1 / A + 1 / B := by positivity
  have hXeq : -1 / sigmaArc a b 0 + -1 / sigmaArc a b (-1) = 1 / A + 1 / B := by
    dsimp [A, B]
    ring
  have hS := Sconst_lt_paper ha hb.le hab hab'
  rw [hXeq] at hS
  have hCS := head_diff_sq_le ha hb hu
  have hT := tsum_tailTerm_nonneg ha hb u
  have hD : 0 < ‖u 0 - u (-1)‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  have hTpos : 0 < ∑' l : ℤ, tailTerm a b u l := by
    by_contra hn
    have hz : (∑' l : ℤ, tailTerm a b u l) = 0 := by linarith
    rw [hz, mul_zero] at hCS
    linarith
  have hlt : ‖u 0 - u (-1)‖ ^ 2 <
      (1 / A + 1 / B) * ∑' l : ℤ, tailTerm a b u l :=
    hCS.trans_lt (mul_lt_mul_of_pos_right hS hTpos)
  have hcoef : A * B / (A + B) = 1 / (1 / A + 1 / B) := by
    have hsum : A + B ≠ 0 := ne_of_gt (add_pos hA hB)
    field_simp
    ring
  change ‖u 0 - u (-1)‖ ^ 2 * (A * B / (A + B)) < _
  rw [hcoef, ← div_eq_mul_one_div]
  exact (div_lt_iff₀ hX).mpr (by simpa only [mul_comm] using hlt)

end KsIndex.ArcEstimateFaithful
