module

public import KsIndexLean.KarcherItem4Diameter

@[expose] public section


/-! Positivity of the horizontal EW differential along radial segments. -/
noncomputable section
namespace KsIndex.KarcherData

/-- A rational positivity estimate for the radial horizontal differential. -/
lemma radial_fraction_re_pos {A B : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) (hA : A < 1)
    {a : ℂ} (ha : ‖a‖ = 1) :
    0 < (((1 : ℂ) - A * a) / (1 + B * a)).re := by
  have hA0 : 0 ≤ A := hB.trans hBA
  have hB1 : B < 1 := hBA.trans_lt hA
  have hr : a.re ≤ 1 := by simpa [ha] using Complex.re_le_norm a
  have hn : a.re ^ 2 + a.im ^ 2 = 1 := by
    have h := Complex.sq_norm a
    rw [ha] at h
    simpa [Complex.normSq_apply, pow_two] using h.symm
  have hd : (1 : ℂ) + B * a ≠ 0 := by
    intro he
    have hh := congrArg norm he
    have heq : (B : ℂ) * a = -1 := by linear_combination he
    have hh := congrArg norm heq
    simp [ha, abs_of_nonneg hB] at hh
    linarith
  rw [Complex.div_re, ← add_div]
  apply div_pos _ (Complex.normSq_pos.mpr hd)
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re, Complex.sub_im,
    Complex.one_im, Complex.mul_im, zero_add, Complex.add_im]
  have hp : 0 < (1 - A) * (1 + B) := mul_pos (by linarith) (by linarith)
  have hc : 0 ≤ (A - B) * (1 - a.re) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonneg hA0 hB, congrArg (fun x : ℝ => A * B * x) hn]

/-- Horizontal complex differential of the Weierstrass immersion. -/
lemma ew_horizontal_complex (k : ℕ) (w d : ℂ) :
    (((ewRealDifferential k w d).1 : ℂ) +
      ((ewRealDifferential k w d).2.1 : ℂ) * Complex.I) =
      (starRingEnd ℂ) (d * etaTarget k w) - d * gauss k w ^ 2 * etaTarget k w := by
  change (((d * coeff1 k w).re : ℂ) + ((d * coeff2 k w).re : ℂ) * Complex.I) = _
  simp only [coeff1, coeff2, Weierstrass.phi1, Weierstrass.phi2]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, map_mul, pow_two] <;> ring

/-- The outward horizontal component of the radial differential has a scalar
rational expression whose denominator is nonzero along nonpunctured rays. -/
lemma ew_radial_horizontal_re {k : ℕ} (hk : 2 ≤ k) (r : ℝ) (e : ℂ) (he : ‖e‖ = 1) :
    (e * (((ewRealDifferential k ((r : ℂ) * e) e).1 : ℂ) +
      ((ewRealDifferential k ((r : ℂ) * e) e).2.1 : ℂ) * Complex.I)).re =
    (k : ℝ) * (((1 : ℂ) - (r : ℂ) ^ (2 * k - 2) * e ^ (2 * k)) /
      (1 + (r : ℂ) ^ (2 * k) * e ^ (2 * k))).re := by
  rw [ew_horizontal_complex]
  have hec : e * (starRingEnd ℂ) e = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, he]
    norm_num
  have hpow : e * e * gauss k ((r : ℂ) * e) ^ 2 =
      (r : ℂ) ^ (2 * k - 2) * e ^ (2 * k) := by
    simp only [gauss, mul_pow, ← pow_mul]
    have h1 : (k - 1) * 2 = 2 * k - 2 := by omega
    have h2 : (k - 1) * 2 + 1 + 1 = 2 * k := by omega
    rw [h1]
    calc
      _ = (r : ℂ) ^ (2*k-2) * (e ^ (2*k-2) * e * e) := by ring
      _ = _ := by rw [← pow_succ, ← pow_succ]; congr 2; omega
  have heq : e * ((starRingEnd ℂ) (e * etaTarget k ((r : ℂ) * e)) -
      e * gauss k ((r : ℂ) * e) ^ 2 * etaTarget k ((r : ℂ) * e)) =
      (starRingEnd ℂ) (etaTarget k ((r : ℂ) * e)) -
        ((r : ℂ) ^ (2*k-2) * e ^ (2*k)) * etaTarget k ((r : ℂ) * e) := by
    rw [map_mul, mul_sub, ← mul_assoc, hec, one_mul]
    rw [show e * (e * gauss k ((r : ℂ) * e) ^ 2 * etaTarget k ((r : ℂ) * e)) =
      (e * e * gauss k ((r : ℂ) * e) ^ 2) * etaTarget k ((r : ℂ) * e) by ring, hpow]
  rw [heq, Complex.sub_re, Complex.conj_re]
  rw [← Complex.sub_re]
  have hr : etaTarget k ((r : ℂ)*e) -
      ((r : ℂ)^(2*k-2)*e^(2*k))*etaTarget k ((r : ℂ)*e) =
      (k : ℂ) * ((1-(r : ℂ)^(2*k-2)*e^(2*k))/(1+(r : ℂ)^(2*k)*e^(2*k))) := by
    simp only [etaTarget, mul_pow, div_eq_mul_inv]
    ring
  rw [hr]
  simp

lemma ew_radial_horizontal_pos {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) {e : ℂ} (he : ‖e‖ = 1) :
    0 < (e * (((ewRealDifferential k ((r : ℂ) * e) e).1 : ℂ) +
      ((ewRealDifferential k ((r : ℂ) * e) e).2.1 : ℂ) * Complex.I)).re := by
  rw [ew_radial_horizontal_re hk r e he]
  apply mul_pos (by positivity)
  have hpow : r ^ (2 * k) ≤ r ^ (2 * k - 2) :=
    pow_le_pow_of_le_one hr hr1.le (by omega)
  have hlt : r ^ (2 * k - 2) < 1 := pow_lt_one₀ hr hr1 (by omega)
  have hh := radial_fraction_re_pos (pow_nonneg hr (2*k)) hpow hlt
    (show ‖e ^ (2*k)‖ = 1 by simp [norm_pow, he])
  simpa only [Complex.ofReal_pow] using hh

lemma unit_fraction_re_zero {a : ℂ} (ha : ‖a‖ = 1) :
    (((1 : ℂ) - a) / (1 + a)).re = 0 := by
  have hn : a.re ^ 2 + a.im ^ 2 = 1 := by
    have h := Complex.sq_norm a
    rw [ha] at h
    simpa [Complex.normSq_apply, pow_two] using h.symm
  rw [Complex.div_re, ← add_div]
  have he : (1 - a).re * (1 + a).re + (1 - a).im * (1 + a).im = 0 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im]
    nlinarith
  rw [he, zero_div]

lemma ew_radial_horizontal_nonneg {k : ℕ} (hk : 2 ≤ k) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {e : ℂ} (he : ‖e‖ = 1) :
    0 ≤ (e * (((ewRealDifferential k ((r : ℂ) * e) e).1 : ℂ) +
      ((ewRealDifferential k ((r : ℂ) * e) e).2.1 : ℂ) * Complex.I)).re := by
  rcases hr1.eq_or_lt with rfl | hlt
  · rw [ew_radial_horizontal_re hk 1 e he]
    simp only [Complex.ofReal_one, one_pow, one_mul]
    rw [unit_fraction_re_zero (by simp [norm_pow, he]), mul_zero]
  · exact (ew_radial_horizontal_pos hk hr hlt he).le

end KsIndex.KarcherData
