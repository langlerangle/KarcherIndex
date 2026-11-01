module

public import KsIndexLean.KarcherHeightStrip

@[expose] public section


/-! The logarithmic coordinate covers the closed fundamental parameter sector,
with its puncture deleted. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

lemma heightCayley_norm_le_one {k : ℕ} {w : ℂ} (hw : w ∉ Surface.punctures k)
    (hi : 0 ≤ (w ^ k).im) : ‖heightCayley k w‖ ≤ 1 := by
  have hn : ‖1 + I * w ^ k‖ ≤ ‖1 - I * w ^ k‖ := by
    have hh : ‖1 + I * w ^ k‖ ^ 2 ≤ ‖1 - I * w ^ k‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
      nlinarith
    nlinarith [norm_nonneg (1 + I * w ^ k), norm_nonneg (1 - I * w ^ k)]
  rw [heightCayley, norm_div]
  exact (div_le_one (norm_pos_iff.mpr (height_factors_ne hw).2)).mpr hn

lemma heightSectorCoordinate_mem_strip {k : ℕ} {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hr : ‖w ^ k‖ ≤ 1)
    (hre : 0 ≤ (w ^ k).re) (him : 0 ≤ (w ^ k).im) :
    heightStrip (heightSectorCoordinate k w) := by
  have hR : 0 ≤ (heightCayley k w).re := by
    rw [heightCayley_re, Complex.normSq_eq_norm_sq]
    exact div_nonneg (by nlinarith [norm_nonneg (w ^ k)]) (Complex.normSq_nonneg _)
  have hI : 0 ≤ (heightCayley k w).im := by
    rw [heightCayley_im]
    exact div_nonneg (mul_nonneg (by norm_num) hre) (Complex.normSq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · change (Complex.log (heightCayley k w)).re ≤ 0
    rw [Complex.log_re]
    exact Real.log_nonpos (norm_nonneg _) (heightCayley_norm_le_one hw him)
  · simpa [heightSectorCoordinate, Complex.log_im] using Complex.arg_nonneg_iff.mpr hI
  · simpa [heightSectorCoordinate, Complex.log_im] using
      Complex.arg_le_pi_div_two_iff.mpr (Or.inl hR)

/-- Every point satisfying the closed-sector conditions has an explicit strip
representative; this includes the center and both radial boundary edges. -/
lemma exists_heightStrip_parameter {k : ℕ} (hk : k ≠ 0) {w : ℂ}
    (hw : w ∉ Surface.punctures k) (hr : ‖w ^ k‖ ≤ 1)
    (hre : 0 ≤ (w ^ k).re) (him : 0 ≤ (w ^ k).im)
    (ha : -(Real.pi / k) < w.arg) (hb : w.arg ≤ Real.pi / k) :
    ∃ ζ, heightStrip ζ ∧ heightSectorParameter k ζ = w := by
  exact ⟨heightSectorCoordinate k w, heightSectorCoordinate_mem_strip hw hr hre him,
    heightSectorParameter_coordinate hk hw ha hb⟩

lemma heightStrip_parameter_norm {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) : ‖heightSectorParameter k ζ‖ ≤ 1 := by
  have hq := heightStrip_exp_re hζ
  have hn : ‖Complex.exp ζ - 1‖ ≤ ‖Complex.exp ζ + 1‖ := by
    have hh : ‖Complex.exp ζ - 1‖ ^ 2 ≤ ‖Complex.exp ζ + 1‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
      nlinarith
    nlinarith [norm_nonneg (Complex.exp ζ - 1), norm_nonneg (Complex.exp ζ + 1)]
  have hu : ‖heightCayleyInverse (Complex.exp ζ)‖ ≤ 1 := by
    rw [heightCayleyInverse, norm_div, norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact (div_le_one (norm_pos_iff.mpr (heightStrip_exp_add_one_ne hζ))).mpr hn
  apply (pow_le_one_iff_of_nonneg (norm_nonneg _) hk).mp
  rw [← norm_pow]
  change ‖(heightCayleyInverse (Complex.exp ζ) ^ ((k : ℂ)⁻¹)) ^ k‖ ≤ 1
  rwa [Complex.cpow_nat_inv_pow _ hk]

/-- The closed angular sector, with the end puncture omitted. -/
def heightSector (k : ℕ) (w : ℂ) : Prop :=
  w ∉ Surface.punctures k ∧ ‖w‖ ≤ 1 ∧ 0 ≤ w.arg ∧ w.arg ≤ Real.pi / (2 * k)

lemma heightSector_powered_quadrant {k : ℕ} (hk : k ≠ 0) {w : ℂ}
    (hw : heightSector k w) : 0 ≤ (w ^ k).re ∧ 0 ≤ (w ^ k).im := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have ha : 0 ≤ (k : ℝ) * w.arg := mul_nonneg hkR.le hw.2.2.1
  have hb : (k : ℝ) * w.arg ≤ Real.pi / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hkR)).mp hw.2.2.2
    nlinarith
  have he : w ^ k = ((‖w‖ ^ k : ℝ) : ℂ) * Complex.exp (((k : ℝ) * w.arg : ℝ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    congr 2
    ring
  rw [he]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact ⟨mul_nonneg (pow_nonneg (norm_nonneg w) _)
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hb⟩),
    mul_nonneg (pow_nonneg (norm_nonneg w) _)
      (Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith [Real.pi_pos]))⟩

lemma heightSector_parameter_mem {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) : heightSector k (heightSectorParameter k ζ) :=
  ⟨heightStrip_parameter_not_puncture hk hζ, heightStrip_parameter_norm hk hζ,
    heightStrip_parameter_arg hk hζ⟩

lemma heightSector_exists_strip {k : ℕ} (hk : k ≠ 0) {w : ℂ}
    (hw : heightSector k w) : ∃ ζ, heightStrip ζ ∧ heightSectorParameter k ζ = w := by
  have hp := heightSector_powered_quadrant hk hw
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  apply exists_heightStrip_parameter hk hw.1
  · rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hw.2.1
  · exact hp.1
  · exact hp.2
  · have := div_pos Real.pi_pos hkR
    linarith [hw.2.2.1]
  · have hh : Real.pi / (2 * (k : ℝ)) ≤ Real.pi / k := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le hkR
      linarith
    exact hw.2.2.2.trans hh

/-- Exact correspondence with the closed sector, not only its interior. -/
lemma heightSector_iff_exists_strip {k : ℕ} (hk : k ≠ 0) {w : ℂ} :
    heightSector k w ↔ ∃ ζ, heightStrip ζ ∧ heightSectorParameter k ζ = w := by
  constructor
  · exact heightSector_exists_strip hk
  · rintro ⟨ζ, hζ, rfl⟩
    exact heightSector_parameter_mem hk hζ

end KsIndex.KarcherData
