module

public import KsIndexLean.KarcherHeightLevelCoordinates
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section


/-! Boundary regularity of the logarithmic coordinates for a fundamental sector. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

/-- The logarithmic parameter domain includes both sector edges and its center. -/
def heightStrip (ζ : ℂ) : Prop := ζ.re ≤ 0 ∧ 0 ≤ ζ.im ∧ ζ.im ≤ Real.pi / 2

lemma heightStrip_exp_re {ζ : ℂ} (hζ : heightStrip ζ) : 0 ≤ (Complex.exp ζ).re := by
  rw [Complex.exp_re]
  exact mul_nonneg (le_of_lt (Real.exp_pos _))
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hζ.2.1, Real.pi_pos], hζ.2.2⟩)

lemma heightStrip_exp_add_one_ne {ζ : ℂ} (hζ : heightStrip ζ) :
    Complex.exp ζ + 1 ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
  linarith [heightStrip_exp_re hζ]

lemma heightStrip_powered_re {ζ : ℂ} (hζ : heightStrip ζ) :
    0 ≤ (heightCayleyInverse (Complex.exp ζ)).re := by
  rw [heightCayleyInverse_re]
  apply div_nonneg
  · rw [Complex.exp_im]
    exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt (Real.exp_pos _))
      (Real.sin_nonneg_of_nonneg_of_le_pi hζ.2.1 (by linarith [hζ.2.2, Real.pi_pos])))
  · exact Complex.normSq_nonneg _

lemma heightStrip_powered_im {ζ : ℂ} (hζ : heightStrip ζ) :
    0 ≤ (heightCayleyInverse (Complex.exp ζ)).im := by
  have hn : ‖Complex.exp ζ‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hζ.1
  rw [heightCayleyInverse_im, Complex.normSq_eq_norm_sq]
  exact div_nonneg (by nlinarith [norm_nonneg (Complex.exp ζ)]) (Complex.normSq_nonneg _)

lemma heightStrip_powered_im_pos {ζ : ℂ} (hζ : heightStrip ζ) (hs : ζ.re < 0) :
    0 < (heightCayleyInverse (Complex.exp ζ)).im := by
  have hn : ‖Complex.exp ζ‖ < 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_lt_one_iff.mpr hs
  rw [heightCayleyInverse_im]
  apply div_pos _ (Complex.normSq_pos.mpr (heightStrip_exp_add_one_ne hζ))
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (Complex.exp ζ)]

/-- Taking the principal root is continuous even at the sector center. -/
lemma continuousAt_heightSectorParameter {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) : ContinuousAt (heightSectorParameter k) ζ := by
  have he : 0 < ((k : ℂ)⁻¹).re := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
    positivity
  have hc := Complex.continuousAt_cpow_const_of_re_pos
    (Or.inl (heightStrip_powered_re hζ)) he
  apply hc.comp (f := fun x => heightCayleyInverse (Complex.exp x))
  unfold heightCayleyInverse
  have hd := heightStrip_exp_add_one_ne hζ
  fun_prop

lemma heightStrip_coordinate_parameter {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) : heightSectorCoordinate k (heightSectorParameter k ζ) = ζ := by
  exact heightSectorCoordinate_parameter hk (heightStrip_exp_add_one_ne hζ)
    (by linarith [hζ.2.1, Real.pi_pos]) (by linarith [hζ.2.2, Real.pi_pos])

lemma heightSectorParameter_injectiveOn {k : ℕ} (hk : k ≠ 0) :
    Set.InjOn (heightSectorParameter k) {ζ | heightStrip ζ} := by
  intro ζ hζ ξ hξ he
  have := congrArg (heightSectorCoordinate k) he
  simpa [heightStrip_coordinate_parameter hk hζ, heightStrip_coordinate_parameter hk hξ] using this

lemma heightCayleyInverse_square {q : ℂ} (hq : q + 1 ≠ 0) :
    1 + heightCayleyInverse q ^ 2 = 4 * q / (q + 1) ^ 2 := by
  unfold heightCayleyInverse
  field_simp
  linear_combination (q - 1) ^ 2 * Complex.I_sq

lemma heightStrip_parameter_not_puncture {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) : heightSectorParameter k ζ ∉ Surface.punctures k := by
  have hp : heightSectorParameter k ζ ^ k = heightCayleyInverse (Complex.exp ζ) :=
    Complex.cpow_nat_inv_pow _ hk
  intro hw
  change heightSectorParameter k ζ ^ (2 * k) = -1 at hw
  rw [Nat.mul_comm 2 k, pow_mul, hp] at hw
  have he := heightCayleyInverse_square (heightStrip_exp_add_one_ne hζ)
  rw [hw] at he
  have hn : 4 * Complex.exp ζ / (Complex.exp ζ + 1) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero ζ))
      (pow_ne_zero _ (heightStrip_exp_add_one_ne hζ))
  apply hn
  linear_combination -he

lemma heightStrip_parameter_ne_zero {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) (hs : ζ.re < 0) : heightSectorParameter k ζ ≠ 0 := by
  intro hw
  have hp : heightSectorParameter k ζ ^ k = heightCayleyInverse (Complex.exp ζ) :=
    Complex.cpow_nat_inv_pow _ hk
  rw [hw, zero_pow hk] at hp
  have hi := heightStrip_powered_im_pos hζ hs
  rw [← hp] at hi
  simp at hi

/-- The inverse parameter is holomorphic along every horizontal strip line
away from its finite right endpoint, including the two horizontal edges. -/
lemma hasDerivAt_heightStrip_parameter {k : ℕ} (hk : 2 ≤ k) {ζ : ℂ}
    (hζ : heightStrip ζ) (hs : ζ.re < 0) :
    HasDerivAt (heightSectorParameter k)
      (I * coeff3 k (heightSectorParameter k ζ))⁻¹ ζ := by
  apply hasDerivAt_heightSectorParameter hk (heightStrip_exp_add_one_ne hζ)
  · exact Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt (heightStrip_powered_im_pos hζ hs)))
  · exact heightStrip_parameter_not_puncture (by omega) hζ
  · exact heightStrip_parameter_ne_zero (by omega) hζ hs

lemma heightStrip_parameter_arg {k : ℕ} (hk : k ≠ 0) {ζ : ℂ}
    (hζ : heightStrip ζ) :
    0 ≤ (heightSectorParameter k ζ).arg ∧
      (heightSectorParameter k ζ).arg ≤ Real.pi / (2 * k) := by
  let u := heightCayleyInverse (Complex.exp ζ)
  by_cases hu : u = 0
  · have he : heightSectorParameter k ζ = 0 := by
      change u ^ ((k : ℂ)⁻¹) = 0
      rw [hu, Complex.zero_cpow (inv_ne_zero (by exact_mod_cast hk))]
    rw [he, Complex.arg_zero]
    exact ⟨le_rfl, by positivity⟩
  have ha : 0 ≤ u.arg := Complex.arg_nonneg_iff.mpr (heightStrip_powered_im hζ)
  have hb : u.arg ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl (heightStrip_powered_re hζ))
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hm : (Complex.log u * (k : ℂ)⁻¹).im = u.arg / k := by
    simp [Complex.mul_im, Complex.log_im, ← Complex.ofReal_natCast,
      ← Complex.ofReal_inv, div_eq_mul_inv]
  have hlow : -Real.pi < (Complex.log u * (k : ℂ)⁻¹).im := by
    rw [hm]
    have := div_nonneg ha hkR.le
    linarith [Real.pi_pos]
  have hbound : u.arg / k ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hkR).mpr
    nlinarith [Real.pi_pos]
  have hhigh : (Complex.log u * (k : ℂ)⁻¹).im ≤ Real.pi := by
    rw [hm]
    linarith [Real.pi_pos]
  have he : (heightSectorParameter k ζ).arg = u.arg / k := by
    change (u ^ ((k : ℂ)⁻¹)).arg = _
    rw [Complex.cpow_def_of_ne_zero hu]
    have hh := congrArg Complex.im (Complex.log_exp hlow hhigh)
    simpa only [Complex.log_im, hm] using hh
  rw [he]
  refine ⟨div_nonneg ha hkR.le, ?_⟩
  calc
    u.arg / k ≤ (Real.pi / 2) / k := div_le_div_of_nonneg_right hb hkR.le
    _ = Real.pi / (2 * k) := by ring

lemma heightStrip_parameter_im_zero {k : ℕ} {ζ : ℂ}
    (hζ : heightStrip ζ) (hs : ζ.re = 0) : (heightSectorParameter k ζ).im = 0 := by
  let u := heightCayleyInverse (Complex.exp ζ)
  have hi : u.im = 0 := by
    dsimp [u]
    rw [heightCayleyInverse_im, Complex.normSq_eq_norm_sq, Complex.norm_exp, hs]
    simp
  have hu : (u.re : ℂ) = u := Complex.ext (by simp) (by simp [hi])
  have hr : 0 ≤ u.re := heightStrip_powered_re hζ
  change (u ^ ((k : ℂ)⁻¹)).im = 0
  rw [← hu, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
    ← Complex.ofReal_cpow hr]
  rfl

end KsIndex.KarcherData
