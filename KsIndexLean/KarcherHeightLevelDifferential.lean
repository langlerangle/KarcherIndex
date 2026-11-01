module

public import KsIndexLean.KarcherRealDifferential
public import KsIndexLean.KarcherHeightCayley

@[expose] public section


/-! Differential identities along height levels in Cayley coordinates.

The final estimate gives a positive, sector-dependent lower bound for the
`y` derivative in the logarithmic Cayley direction. These are local differential
statements; global injectivity and embeddedness require separate arguments. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- The inverse Cayley transformation in the powered parameter u=w^k. -/
def heightCayleyInverse (q : ℂ) : ℂ := -I * (q - 1) / (q + 1)

lemma heightCayleyInverse_apply {q : ℂ} (hq : q + 1 ≠ 0) :
    (1 + I * heightCayleyInverse q) / (1 - I * heightCayleyInverse q) = q := by
  have hd : 1 - I * heightCayleyInverse q = 2 / (q + 1) := by
    unfold heightCayleyInverse
    field_simp
    linear_combination (q - 1) * Complex.I_sq
  rw [hd]
  unfold heightCayleyInverse
  field_simp
  linear_combination -(q - 1) * Complex.I_sq

lemma heightCayleyInverse_re (q : ℂ) :
    (heightCayleyInverse q).re = 2 * q.im / Complex.normSq (q + 1) := by
  unfold heightCayleyInverse
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.add_re, Complex.add_im]
  ring

lemma heightCayleyInverse_im (q : ℂ) :
    (heightCayleyInverse q).im = (1 - Complex.normSq q) / Complex.normSq (q + 1) := by
  unfold heightCayleyInverse
  rw [Complex.div_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.add_re, Complex.add_im, Complex.normSq_apply]
  ring

lemma heightCayleyInverse_norm_lt_one {q : ℂ} (hq : 0 < q.re) :
    ‖heightCayleyInverse q‖ < 1 := by
  have hn : ‖q - 1‖ < ‖q + 1‖ := by
    have hsq : ‖q - 1‖ ^ 2 < ‖q + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      nlinarith
    nlinarith [norm_nonneg (q - 1), norm_nonneg (q + 1)]
  rw [heightCayleyInverse, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hn)).mpr hn

/-- In the open quarter disk, the inverse Cayley coordinate is again in the
open quarter disk. This is the algebra behind straight height-coordinate lines. -/
lemma heightCayleyInverse_quarter {q : ℂ}
    (hr : 0 < q.re) (hi : 0 < q.im) (hn : ‖q‖ < 1) :
    0 < (heightCayleyInverse q).re ∧ 0 < (heightCayleyInverse q).im ∧
      ‖heightCayleyInverse q‖ < 1 := by
  have hq : q + 1 ≠ 0 := by
    intro hh
    have hh' := congrArg Complex.re hh
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh'
    linarith
  have hd := Complex.normSq_pos.mpr hq
  refine ⟨?_, ?_, heightCayleyInverse_norm_lt_one hr⟩
  · rw [heightCayleyInverse_re]
    positivity
  · rw [heightCayleyInverse_im, Complex.normSq_eq_norm_sq]
    exact div_pos (by nlinarith [norm_nonneg q]) hd

/-- Derivative of the Cayley coordinate in the direction of increasing its
logarithmic modulus, with its argument fixed. -/
lemma heightCayley_log_direction {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hw0 : w ≠ 0) :
    (I * coeff3 k w * heightCayley k w) * (I * coeff3 k w)⁻¹ = heightCayley k w := by
  have hg : gauss k w ≠ 0 := pow_ne_zero _ hw0
  have hc : coeff3 k w ≠ 0 := by
    unfold coeff3 Weierstrass.phi3
    exact mul_ne_zero (mul_ne_zero (by norm_num) hg) (etaTarget_ne_zero hk hw)
  field_simp

/-- Along a log-Cayley horizontal direction the height derivative vanishes,
and the y derivative has this elementary Gauss-map expression. -/
lemma ew_height_level_y {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hw0 : w ≠ 0) :
    (ewRealDifferential k w (I * coeff3 k w)⁻¹).2.1 =
      ((gauss k w + (gauss k w)⁻¹) / 2).re := by
  change (((I * coeff3 k w)⁻¹) * coeff2 k w).re = _
  congr 1
  have hg : gauss k w ≠ 0 := pow_ne_zero _ hw0
  have hη := etaTarget_ne_zero hk hw
  unfold coeff2 coeff3 Weierstrass.phi2 Weierstrass.phi3
  field_simp
  ring

lemma ew_height_level_z {k : ℕ} (hk : 2 ≤ k) {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hw0 : w ≠ 0) :
    (ewRealDifferential k w (I * coeff3 k w)⁻¹).2.2 = 0 := by
  have hg : gauss k w ≠ 0 := pow_ne_zero _ hw0
  have hc : coeff3 k w ≠ 0 := by
    unfold coeff3 Weierstrass.phi3
    exact mul_ne_zero (mul_ne_zero (by norm_num) hg) (etaTarget_ne_zero hk hw)
  change (((I * coeff3 k w)⁻¹) * coeff3 k w).re = 0
  rw [mul_inv_rev, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  simp

lemma gauss_height_level_y_pos {g : ℂ} (hg : 0 < g.re) :
    0 < ((g + g⁻¹) / 2).re := by
  have hg0 : g ≠ 0 := by intro hh; simp [hh] at hg
  have hn := Complex.normSq_pos.mpr hg0
  have hi : 0 < (g⁻¹).re := by rw [Complex.inv_re]; exact div_pos hg hn
  simp only [Complex.div_ofNat_re, Complex.add_re]
  positivity

/-- A quantitative lower bound independent of the modulus of g. -/
lemma polar_height_level_y_lower {r θ : ℝ} (hr : 0 < r) (hθ : 0 ≤ Real.cos θ) :
    Real.cos θ ≤ (((r : ℂ) * Complex.exp ((θ : ℂ) * I) +
      ((r : ℂ) * Complex.exp ((θ : ℂ) * I))⁻¹) / 2).re := by
  have hn : Complex.normSq ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [Complex.div_ofNat_re, Complex.add_re, Complex.inv_re, hn,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hh : 2 * Real.cos θ - r * Real.cos θ ≤ r * Real.cos θ / r ^ 2 := by
    apply (le_div_iff₀ hr2).mpr
    nlinarith [mul_nonneg (mul_nonneg hr.le hθ) (sq_nonneg (r - 1))]
  linarith

/-- The slope is uniformly positive throughout a fundamental parameter sector,
including its straight sides away from the center and its puncture. -/
theorem ew_height_level_y_uniform {k : ℕ} (hk : 2 ≤ k) {r θ : ℝ}
    (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / (2 * k))
    (hw : (r : ℂ) * Complex.exp ((θ : ℂ) * I) ∉ Surface.punctures k) :
    0 < Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k))) ∧
    Real.cos ((k - 1 : ℕ) * (Real.pi / (2 * k))) ≤
      (ewRealDifferential k ((r : ℂ) * Complex.exp ((θ : ℂ) * I))
        (I * coeff3 k ((r : ℂ) * Complex.exp ((θ : ℂ) * I)))⁻¹).2.1 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hks : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hν0 : 0 ≤ ((k - 1 : ℕ) : ℝ) * θ := mul_nonneg (Nat.cast_nonneg _) hθ0
  have hν : ((k - 1 : ℕ) : ℝ) * θ ≤
      ((k - 1 : ℕ) : ℝ) * (Real.pi / (2 * k)) :=
    mul_le_mul_of_nonneg_left hθ1 (Nat.cast_nonneg _)
  have hmax : ((k - 1 : ℕ) : ℝ) * (Real.pi / (2 * k)) < Real.pi / 2 := by
    rw [hks]
    have he : ((k : ℝ) - 1) * (Real.pi / (2 * k)) =
        Real.pi / 2 - Real.pi / (2 * k) := by field_simp
    rw [he]
    have : 0 < Real.pi / (2 * (k : ℝ)) := by positivity
    linarith
  have hmax0 : 0 ≤ ((k - 1 : ℕ) : ℝ) * (Real.pi / (2 * k)) := by positivity
  have hp := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hmax⟩
  refine ⟨hp, ?_⟩
  have hw0 : (r : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hr.ne') (Complex.exp_ne_zero _)
  rw [ew_height_level_y hk hw hw0]
  have he : gauss k ((r : ℂ) * Complex.exp ((θ : ℂ) * I)) =
      ((r ^ (k - 1) : ℝ) : ℂ) * Complex.exp ((((k - 1 : ℕ) : ℝ) * θ : ℝ) * I) := by
    unfold gauss
    rw [mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_pow]
    congr 2
    push_cast
    ring
  rw [he]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hν0
    (by linarith [Real.pi_pos] : ((k - 1 : ℕ) : ℝ) * (Real.pi / (2 * k)) ≤ Real.pi) hν
  exact hc.trans (polar_height_level_y_lower (pow_pos hr _) (hp.le.trans hc))

end KsIndex.KarcherData
