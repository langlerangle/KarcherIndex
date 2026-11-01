module

public import KsIndexLean.KarcherPlaneEstimates

@[expose] public section


/-! Signed horizontal differential relative to a vertical symmetry plane. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- In coordinates rotated to a distinguished plane, the signed EW
radial differential is the imaginary part of a single rational function. -/
lemma ew_plane_radial_fraction {k : ℕ} (hk : 2 ≤ k) (r : ℝ) (a q : ℂ)
    (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1) :
    (a * (((ewRealDifferential k ((r : ℂ)*a*q) (a*q)).1 : ℂ) +
      ((ewRealDifferential k ((r : ℂ)*a*q) (a*q)).2.1 : ℂ)*I)).im =
    (k : ℝ) * (((r : ℂ)^(2*k-2)*q^(2*k-1)-q) /
      (1-(r : ℂ)^(2*k)*q^(2*k))).im := by
  rw [ew_horizontal_complex]
  have hac : a * (starRingEnd ℂ) a = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, ha]; norm_num
  have hη : etaTarget k ((r : ℂ)*a*q) =
      (k : ℂ) / (1-(r : ℂ)^(2*k)*q^(2*k)) := by
    simp only [etaTarget, mul_pow, hak]; congr 1; ring
  have hg : a * (a*q) * gauss k ((r : ℂ)*a*q)^2 =
      -((r : ℂ)^(2*k-2)*q^(2*k-1)) := by
    simp only [gauss, ← pow_mul, mul_pow]
    rw [show (k-1)*2 = 2*k-2 by omega]
    calc
      _ = (r : ℂ)^(2*k-2) * (a^(2*k-2)*a*a) * (q^(2*k-2)*q) := by ring
      _ = _ := by
        rw [← pow_succ, ← pow_succ, ← pow_succ,
          show 2*k-2+1+1 = 2*k by omega,
          show 2*k-2+1 = 2*k-1 by omega, hak]
        ring
  have hc (z : ℂ) : a * (starRingEnd ℂ) ((a*q)*z) =
      (starRingEnd ℂ) (q*z) := by
    simp only [map_mul]
    calc
      _ = (a * (starRingEnd ℂ) a) * ((starRingEnd ℂ) q * (starRingEnd ℂ) z) := by ring
      _ = _ := by rw [hac, one_mul]
  rw [mul_sub, hc, ← mul_assoc, ← mul_assoc, hg, neg_mul, sub_neg_eq_add,
    Complex.add_im, Complex.conj_im]
  rw [show -(q * etaTarget k ((r : ℂ)*a*q)).im +
      ((r : ℂ)^(2*k-2)*q^(2*k-1)*etaTarget k ((r : ℂ)*a*q)).im =
      (((r : ℂ)^(2*k-2)*q^(2*k-1)-q)*etaTarget k ((r : ℂ)*a*q)).im by
        simp only [sub_mul, Complex.sub_im]; ring]
  rw [hη, show ((r : ℂ)^(2*k-2)*q^(2*k-1)-q) *
      ((k : ℂ)/(1-(r : ℂ)^(2*k)*q^(2*k))) =
      (k : ℂ)*(((r : ℂ)^(2*k-2)*q^(2*k-1)-q)/(1-(r : ℂ)^(2*k)*q^(2*k))) by ring]
  simp

/-- Imaginary part of the rotated radial fraction, with its exact denominator. -/
lemma plane_fraction_im (A B t : ℝ) (n : ℕ) :
    (((A : ℂ)*Complex.exp (((n : ℝ)*t : ℝ)*I) - Complex.exp ((t : ℂ)*I)) /
      (1-(B : ℂ)*Complex.exp ((((n : ℝ)+1)*t : ℝ)*I))).im =
    ((A-B)*Real.sin ((n : ℝ)*t) - (1-A*B)*Real.sin t) /
      Complex.normSq (1-(B : ℂ)*Complex.exp ((((n : ℝ)+1)*t : ℝ)*I)) := by
  rw [Complex.div_im, ← sub_div]
  congr 1
  simp only [Complex.sub_im, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, sub_zero, add_zero]
  rw [add_mul, one_mul, Real.sin_add, Real.cos_add]
  have ht := Real.sin_sq_add_cos_sq t
  have hn := Real.sin_sq_add_cos_sq ((n : ℝ)*t)
  linear_combination A*B*Real.sin t * hn - B*Real.sin ((n : ℝ)*t) * ht

/-- Exact signed EW radial differential at a distinguished plane angle. -/
lemma ew_plane_radial_im {k : ℕ} (hk : 2 ≤ k) (r t : ℝ) (a : ℂ)
    (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1) :
    (a * (((ewRealDifferential k ((r : ℂ)*a*Complex.exp ((t : ℂ)*I))
      (a*Complex.exp ((t : ℂ)*I))).1 : ℂ) +
      ((ewRealDifferential k ((r : ℂ)*a*Complex.exp ((t : ℂ)*I))
        (a*Complex.exp ((t : ℂ)*I))).2.1 : ℂ)*I)).im =
    (k : ℝ) * ((r^(2*k-2)-r^(2*k))*Real.sin ((2*k-1 : ℕ)*t) -
      (1-r^(4*k-2))*Real.sin t) /
      Complex.normSq (1-(r : ℂ)^(2*k)*Complex.exp (((2*k : ℕ)*t : ℝ)*I)) := by
  rw [ew_plane_radial_fraction hk r a _ ha hak]
  have hp (n : ℕ) : Complex.exp ((t : ℂ)*I)^n =
      Complex.exp (((n : ℝ)*t : ℝ)*I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hp, hp]
  have hn : ((2*k : ℕ) : ℝ) = ((2*k-1 : ℕ) : ℝ)+1 := by
    exact_mod_cast (show 2*k = (2*k-1)+1 by omega)
  rw [hn, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    plane_fraction_im (r^(2*k-2)) (r^(2*k)) t (2*k-1)]
  have hab : r^(2*k-2)*r^(2*k) = r^(4*k-2) := by
    rw [← pow_add]; congr 1; omega
  rw [hab]
  push_cast
  ring

/-- Strict signed differential on the upper parameter half-plane. -/
lemma ew_plane_radial_im_neg {k : ℕ} (hk : 2 ≤ k) {r t : ℝ} {a : ℂ}
    (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1) (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : 0 < t) (htpi : t < Real.pi) :
    (a * (((ewRealDifferential k ((r : ℂ)*a*Complex.exp ((t : ℂ)*I))
      (a*Complex.exp ((t : ℂ)*I))).1 : ℂ) +
      ((ewRealDifferential k ((r : ℂ)*a*Complex.exp ((t : ℂ)*I))
        (a*Complex.exp ((t : ℂ)*I))).2.1 : ℂ)*I)).im < 0 := by
  rw [ew_plane_radial_im hk r t a ha hak]
  have hd : 1-(r : ℂ)^(2*k)*Complex.exp (((2*k : ℕ)*t : ℝ)*I) ≠ 0 := by
    have hnorm : ‖(r : ℂ)^(2*k)*Complex.exp (((2*k : ℕ)*t : ℝ)*I)‖ < 1 := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact pow_lt_one₀ hr hr1 (by omega)
    intro he
    have heq := sub_eq_zero.mp he
    rw [← heq, norm_one] at hnorm
    exact (lt_irrefl _ hnorm)
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by positivity) (plane_radial_numerator_neg hk hr hr1 ht htpi))
    (Complex.normSq_pos.mpr hd)

/-- At a nonpunctured unit-radius endpoint the same algebraic differential
has zero signed component. This is an identity of the rational EW expression;
regularity at the parameter still requires exclusion of punctures. -/
lemma ew_plane_radial_im_one {k : ℕ} (hk : 2 ≤ k) (t : ℝ) (a : ℂ)
    (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1) :
    (a * (((ewRealDifferential k (a*Complex.exp ((t : ℂ)*I))
      (a*Complex.exp ((t : ℂ)*I))).1 : ℂ) +
      ((ewRealDifferential k (a*Complex.exp ((t : ℂ)*I))
        (a*Complex.exp ((t : ℂ)*I))).2.1 : ℂ)*I)).im = 0 := by
  simpa using ew_plane_radial_im hk 1 t a ha hak

end KsIndex.KarcherData
