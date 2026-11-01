module

public import KsIndexLean.AlphaStieltjesZChain
public import KsIndexLean.AlphaTrialResidualSplit

@[expose] public section


/-! # Base indices and recurrence denominators for the trial

The 25 trial terms have parity-dependent base shifts and chain lengths satisfying
`r_i + 2 k_i = r_g`. This file proves their concrete bounds and the denominator
nonvanishing needed for `z = n + 9/2` and `z = 13/3`.
-/

noncomputable section
namespace KsIndex.OppositeHalf
open CircleQ PowerArc KsIndex.AlphaRemarkTrial

/-- Parity-group base shift: `−6` for even shifts, `−5` for odd. -/
def baseShift (i : Fin 25) : ℤ := if shift i % 2 = 0 then -6 else -5

/-- Chain length from the term to its group base. -/
def chainLen (i : Fin 25) : ℕ := ((shift i - baseShift i) / 2).toNat

/-- The group-base transform index `r_g = 9 − baseShift`. -/
def baseR (i : Fin 25) : ℝ := 9 - (baseShift i : ℝ)

lemma chainLen_rel (i : Fin 25) :
    (9 - (shift i : ℝ)) + 2 * chainLen i = baseR i := by
  fin_cases i <;> simp [shift, baseShift, chainLen, baseR] <;> norm_num

lemma chainLen_le_six (i : Fin 25) : chainLen i ≤ 6 := by
  fin_cases i <;> simp [shift, baseShift, chainLen] <;> norm_num

lemma exponent_le_baseterm (i : Fin 25) : exponent i ≤ 9 - (shift i : ℝ) := by
  fin_cases i <;> norm_num [shift, exponent]

/-- No integer equals `a / b` when `b` does not divide `a`. -/
lemma not_int_eq_div {a b : ℤ} (hb : 0 < b) (hnd : ¬ (b ∣ a)) (m : ℤ) :
    (m : ℝ) ≠ (a : ℝ) / (b : ℝ) := by
  intro hc
  apply hnd
  have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hmb : (m : ℝ) * b = a := by
    field_simp at hc
    linarith [hc]
  refine ⟨m, ?_⟩
  have : (a : ℝ) = (b : ℝ) * m := by linarith [hmb]
  exact_mod_cast this

lemma fracL1 (m : ℤ) : (m : ℝ) ≠ 35676382/20000000 := by
  have h := not_int_eq_div (a := 35676382) (b := 20000000) (by norm_num) (by decide) m
  intro hc; apply h; rw [hc]; norm_num

lemma fracL2 (m : ℤ) : (m : ℝ) ≠ 25676382/20000000 := by
  have h := not_int_eq_div (a := 25676382) (b := 20000000) (by norm_num) (by decide) m
  intro hc; apply h; rw [hc]; norm_num

lemma fracL3 (m : ℤ) : (m : ℝ) ≠ 34323618/20000000 := by
  have h := not_int_eq_div (a := 34323618) (b := 20000000) (by norm_num) (by decide) m
  intro hc; apply h; rw [hc]; norm_num

lemma fracL4 (m : ℤ) : (m : ℝ) ≠ 24323618/20000000 := by
  have h := not_int_eq_div (a := 24323618) (b := 20000000) (by norm_num) (by decide) m
  intro hc; apply h; rw [hc]; norm_num

lemma offset_cases (i : Fin 25) :
    (baseR i - exponent i) / 2 - 11/2 = (35676382/20000000 : ℝ) ∨
    (baseR i - exponent i) / 2 - 11/2 = (25676382/20000000 : ℝ) ∨
    (baseR i - exponent i) / 2 - 11/2 = (34323618/20000000 : ℝ) ∨
    (baseR i - exponent i) / 2 - 11/2 = (24323618/20000000 : ℝ) := by
  fin_cases i <;>
    simp only [baseR, baseShift, shift, exponent] <;>
    first
      | (left; norm_num; done)
      | (right; left; norm_num; done)
      | (right; right; left; norm_num; done)
      | (right; right; right; norm_num; done)

/-- The four fractional offsets are never integers: the uniform supplier for
the `z = n + 9/2` denominator family. -/
lemma frac_offset_not_int (i : Fin 25) (m : ℤ) :
    (m : ℝ) ≠ (baseR i - exponent i) / 2 - 11 / 2 := by
  rcases offset_cases i with h | h | h | h <;> rw [h]
  · exact fracL1 m
  · exact fracL2 m
  · exact fracL3 m
  · exact fracL4 m

/-- Uniform `z = n + 9/2` denominator discharge, every `n`, every step. -/
lemma denom_nFamily (i : Fin 25) (n : ℤ) (u : ℕ) :
    ((n : ℝ) + 9/2) + u + 1 - (baseR i - exponent i) / 2 ≠ 0 :=
  denom_ne_zero_nFamily n u (frac_offset_not_int i)

/-- Small-z (`z = 13/3`) denominator discharge, per chain step. -/
lemma denom_smallz (i : Fin 25) (u : ℕ) (hu : u < chainLen i) :
    (13/3 : ℝ) + u + 1 - (baseR i - exponent i) / 2 ≠ 0 := by
  have h6 : u < 6 := lt_of_lt_of_le hu (chainLen_le_six i)
  clear hu
  fin_cases i <;>
    interval_cases u <;>
    norm_num [baseR, baseShift, shift, exponent]

end KsIndex.OppositeHalf
