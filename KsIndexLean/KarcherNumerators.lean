module

public import KsIndexLean.KarcherPolynomialRoots

@[expose] public section


/-! Actual normalized numerator polynomials, bound to the existing Weierstrass coefficients. -/
open Polynomial
noncomputable section
namespace KsIndex.KarcherData

def numeratorPoly1 (k : ℕ) : ℂ[X] := C (k : ℂ) * (1 - X ^ (2 * k - 2))
def numeratorPoly2 (k : ℕ) : ℂ[X] := C (Complex.I * (k : ℂ)) * (1 + X ^ (2 * k - 2))
def numeratorPoly3 (k : ℕ) : ℂ[X] := C (2 * (k : ℂ)) * X ^ (k - 1)

lemma numeratorPoly1_eval {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    (numeratorPoly1 k).eval w = (1 - (gauss k w) ^ 2) * (k : ℂ) := by
  simp only [numeratorPoly1, eval_mul, eval_C, eval_sub, eval_one, eval_pow, eval_X]
  rw [show 2 * k - 2 = (k - 1) * 2 by omega, pow_mul]
  unfold gauss
  ring
lemma numeratorPoly2_eval {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    (numeratorPoly2 k).eval w = Complex.I * (1 + (gauss k w) ^ 2) * (k : ℂ) := by
  simp only [numeratorPoly2, eval_mul, eval_C, eval_add, eval_one, eval_pow, eval_X]
  rw [show 2 * k - 2 = (k - 1) * 2 by omega, pow_mul]
  unfold gauss
  ring
lemma numeratorPoly3_eval (k : ℕ) (w : ℂ) :
    (numeratorPoly3 k).eval w = 2 * gauss k w * (k : ℂ) := by
  simp only [numeratorPoly3, eval_mul, eval_C, eval_pow, eval_X, gauss]
  ring

lemma numeratorPoly1_degree {k : ℕ} (hk : 2 ≤ k) : (numeratorPoly1 k).degree < ↑(2 * k) := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hne : 2 * k - 2 ≠ n := by omega
  simp only [numeratorPoly1, coeff_C_mul, coeff_sub, coeff_one, coeff_X_pow,
    ite_eq_right hn0, ite_eq_right hne.symm, sub_self, mul_zero]
lemma numeratorPoly2_degree {k : ℕ} (hk : 2 ≤ k) : (numeratorPoly2 k).degree < ↑(2 * k) := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hne : 2 * k - 2 ≠ n := by omega
  simp only [numeratorPoly2, coeff_C_mul, coeff_add, coeff_one, coeff_X_pow,
    ite_eq_right hn0, ite_eq_right hne.symm, add_zero, mul_zero]
lemma numeratorPoly3_degree {k : ℕ} (hk : 2 ≤ k) : (numeratorPoly3 k).degree < ↑(2 * k) := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  have hne : k - 1 ≠ n := by omega
  simp only [numeratorPoly3, coeff_C_mul, coeff_X_pow, ite_eq_right hne.symm, mul_zero]

lemma numeratorPoly1_div_eq_coeff1 {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    (numeratorPoly1 k).eval w / (denominatorPoly k).eval w = coeff1 k w := by
  rw [numeratorPoly1_eval hk, denominatorPoly_eval]
  simp only [coeff1, Weierstrass.phi1, etaTarget, denominator, div_eq_mul_inv]
  ring
lemma numeratorPoly2_div_eq_coeff2 {k : ℕ} (hk : 2 ≤ k) (w : ℂ) :
    (numeratorPoly2 k).eval w / (denominatorPoly k).eval w = coeff2 k w := by
  rw [numeratorPoly2_eval hk, denominatorPoly_eval]
  simp only [coeff2, Weierstrass.phi2, etaTarget, denominator, div_eq_mul_inv]
  ring
lemma numeratorPoly3_div_eq_coeff3 (k : ℕ) (w : ℂ) :
    (numeratorPoly3 k).eval w / (denominatorPoly k).eval w = coeff3 k w := by
  rw [numeratorPoly3_eval, denominatorPoly_eval]
  simp only [coeff3, Weierstrass.phi3, etaTarget, denominator, div_eq_mul_inv]
  ring

end KsIndex.KarcherData
