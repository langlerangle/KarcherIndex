module

public import KsIndexLean.AlphaResidualPairAlgebra

@[expose] public section


/-! Uniform bounds for the paired inner-residual tail coefficients.

The constant leading term in the symmetric coefficient is removed before
estimating. For a cutoff `X ≥ 1` satisfying `4 * n^2 < X^2`, the two
coefficients are bounded by explicit multiples of `1/x` and `1/x^2` for `x ≥ X`.
-/
namespace KsIndex.AlphaResidual

theorem quadratic_damping_bound (c X x : ℝ) (hc : 0 ≤ c)
    (hX : 0 ≤ X) (hx : X ≤ x) (hcut : c < X ^ 2) :
    x ^ 2 / (x ^ 2 - c) ≤ X ^ 2 / (X ^ 2 - c) := by
  have hs : X ^ 2 ≤ x ^ 2 := by nlinarith
  have hd : 0 < x ^ 2 - c := by linarith
  have hD : 0 < X ^ 2 - c := by linarith
  apply (div_le_div_iff₀ hd hD).2
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hs)]

noncomputable def innerPairA (n x : ℝ) : ℝ :=
  x * ((2 + 12 * n) + (8 - 48 * n) / (9 * x ^ 2 - 1)) / (x ^ 2 - 4 * n ^ 2)

noncomputable def innerPairBError (n x : ℝ) : ℝ :=
  (24 * n ^ 2 + 4 * n + (16 * n - 24 * x ^ 2) / (9 * x ^ 2 - 1)) /
    (x ^ 2 - 4 * n ^ 2)

noncomputable def innerPairAMajorant (n X : ℝ) : ℝ :=
  (2 + 12 * |n| + (8 + 48 * |n|) / (9 * X ^ 2 - 1)) *
    (X ^ 2 / (X ^ 2 - 4 * n ^ 2))

noncomputable def innerPairBMajorant (n X : ℝ) : ℝ :=
  (24 * n ^ 2 + 4 * |n| + (16 * |n| + 24 * X ^ 2) / (9 * X ^ 2 - 1)) *
    (X ^ 2 / (X ^ 2 - 4 * n ^ 2))

theorem inner_pair_a_bound (n X x : ℝ) (hX : 1 ≤ X) (hx : X ≤ x)
    (hcut : 4 * n ^ 2 < X ^ 2) :
    |innerPairA n x| ≤ innerPairAMajorant n X / x := by
  have hx0 : 0 < x := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hs : X ^ 2 ≤ x ^ 2 := by nlinarith
  have hd : 0 < x ^ 2 - 4 * n ^ 2 := by linarith
  have hD : 0 < X ^ 2 - 4 * n ^ 2 := by linarith
  have hp : 0 < 9 * X ^ 2 - 1 := by nlinarith
  have hp' : 0 < 9 * x ^ 2 - 1 := by nlinarith
  have hsmall : |8 - 48 * n| ≤ 8 + 48 * |n| := by
    have hh := abs_sub_le 8 0 (48*n)
    norm_num only [sub_zero, zero_sub, abs_neg, abs_mul] at hh
    exact hh
  have hlarge : |2 + 12 * n| ≤ 2 + 12 * |n| := by
    have hh := abs_add_le (2 : ℝ) (12*n)
    norm_num only [abs_mul] at hh
    exact hh
  have hfrac : |(8 - 48 * n) / (9 * x ^ 2 - 1)| ≤
      (8 + 48 * |n|) / (9 * X ^ 2 - 1) := by
    rw [abs_div, abs_of_pos hp']
    exact (div_le_div_of_nonneg_right hsmall hp'.le).trans
      (div_le_div_of_nonneg_left (by positivity) hp (by nlinarith))
  have hnum := (abs_add_le (2+12*n) ((8-48*n)/(9*x^2-1))).trans
    (add_le_add hlarge hfrac)
  have hratio := quadratic_damping_bound (4*n^2) X x (by positivity) hX0 hx hcut
  have hfactor : x / (x^2-4*n^2) ≤ (X^2/(X^2-4*n^2))/x := by
    apply (le_div_iff₀ hx0).2
    convert! hratio using 1; ring
  unfold innerPairA innerPairAMajorant
  rw [abs_div, abs_mul, abs_of_pos hx0, abs_of_pos hd]
  calc
    _ = |(2+12*n)+(8-48*n)/(9*x^2-1)| * (x/(x^2-4*n^2)) := by ring
    _ ≤ (2+12*|n|+(8+48*|n|)/(9*X^2-1)) * ((X^2/(X^2-4*n^2))/x) := by
      exact mul_le_mul hnum hfactor (by positivity) (by positivity)
    _ = _ := by ring

theorem inner_pair_b_error_bound (n X x : ℝ) (hX : 1 ≤ X) (hx : X ≤ x)
    (hcut : 4 * n ^ 2 < X ^ 2) :
    |innerPairBError n x| ≤ innerPairBMajorant n X / x ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hs : X ^ 2 ≤ x ^ 2 := by nlinarith
  have hd : 0 < x ^ 2 - 4 * n ^ 2 := by linarith
  have hD : 0 < X ^ 2 - 4 * n ^ 2 := by linarith
  have hp : 0 < 9 * X ^ 2 - 1 := by nlinarith
  have hp' : 0 < 9 * x ^ 2 - 1 := by nlinarith
  have hpoly : x ^ 2 / (9*x^2-1) ≤ X ^ 2 / (9*X^2-1) := by
    apply (div_le_div_iff₀ hp' hp).2
    nlinarith
  have hsmall : |16*n-24*x^2| ≤ 16*|n|+24*x^2 := by
    have hh := abs_sub_le (16*n) 0 (24*x^2)
    rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 24*x^2)] at hh
    norm_num only [abs_mul] at hh
    exact hh
  have hlarge : |24*n^2+4*n| ≤ 24*n^2+4*|n| := by
    have hh := abs_add_le (24*n^2) (4*n)
    rw [abs_of_nonneg (by positivity : 0 ≤ 24*n^2)] at hh
    norm_num only [abs_mul] at hh
    exact hh
  have hfrac : |(16*n-24*x^2)/(9*x^2-1)| ≤
      (16*|n|+24*X^2)/(9*X^2-1) := by
    rw [abs_div, abs_of_pos hp']
    calc
      _ ≤ (16*|n|+24*x^2)/(9*x^2-1) := div_le_div_of_nonneg_right hsmall hp'.le
      _ = (16*|n|)/(9*x^2-1)+24*(x^2/(9*x^2-1)) := by ring
      _ ≤ (16*|n|)/(9*X^2-1)+24*(X^2/(9*X^2-1)) := by
        exact add_le_add
          (div_le_div_of_nonneg_left (by positivity) hp (by nlinarith))
          (mul_le_mul_of_nonneg_left hpoly (by norm_num))
      _ = _ := by ring
  have hnum := (abs_add_le (24*n^2+4*n) ((16*n-24*x^2)/(9*x^2-1))).trans
    (add_le_add hlarge hfrac)
  have hratio := quadratic_damping_bound (4*n^2) X x (by positivity) hX0 hx hcut
  have hfactor : 1/(x^2-4*n^2) ≤ (X^2/(X^2-4*n^2))/x^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hx0)).2
    convert! hratio using 1; ring
  unfold innerPairBError innerPairBMajorant
  rw [abs_div, abs_of_pos hd]
  calc
    _ = |24*n^2+4*n+(16*n-24*x^2)/(9*x^2-1)| * (1/(x^2-4*n^2)) := by ring
    _ ≤ (24*n^2+4*|n|+(16*|n|+24*X^2)/(9*X^2-1)) *
        ((X^2/(X^2-4*n^2))/x^2) := by
      exact mul_le_mul hnum hfactor (by positivity) (by positivity)
    _ = _ := by ring

end KsIndex.AlphaResidual
