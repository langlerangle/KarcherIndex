module

public import KsIndexLean.AlphaStarCertification
public import KsIndexLean.AlphaFourModeCauchy

@[expose] public section


/-! A residual certificate for positivity of the circle form.

The head coefficient is the only negative diagonal direction. A trial field
with head coefficient one therefore gives a positive-side certificate if its
energy exceeds the squared dual norm of its residual on the head-zero space.
The residual bound is an explicit hypothesis: this module does not certify
any numerical spectral point by itself.
-/
noncomputable section
namespace KsIndex.AlphaResidual
open CircleQ Statements

/-- Negative energy of a head-normalized trial field certifies the negative sign;
unit normalization of its full sequence is unnecessary. -/
theorem gam_neg_of_head_trial {s : ℝ} {w : ℤ → ℂ}
    (hw : MemDom w) (hw0 : w 0 = 1) (hq : Qform s w < 0) : gam s < 0 := by
  have hne : w ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hw0] at this
  exact lt_of_le_of_lt (GammaOne.gam_le_div hw (normSq_pos hw hne))
    (div_neg_of_neg_of_pos hq (normSq_pos hw hne))

lemma qform_nonneg_of_head_zero {s : ℝ} {z : ℤ → ℂ}
    (hz : MemDom z) (hzero : z 0 = 0) : 0 ≤ Qform s z := by
  by_cases h : z = 0
  · subst z
    rw [Qform_zero]
  · exact (Qform_pos_of_head_zero hz hzero (Function.ne_iff.mp h)).le

/-- Scalar completion of the square, without square roots. -/
lemma residual_young {e q c r : ℝ} (he : 0 ≤ e) (hq : 0 ≤ q)
    (hc : 0 ≤ c) (hr : r ^ 2 ≤ c * e * q) :
    0 ≤ c * e + 2 * r + q := by
  have hce : 0 ≤ c * e := mul_nonneg hc he
  by_contra h
  have hn : c * e + 2 * r + q < 0 := lt_of_not_ge h
  have hrneg : r < 0 := by linarith
  have hsq : (c * e + q) ^ 2 < (2 * r) ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg (c * e - q)]

/-- A strict residual margin proves positivity on the entire form domain. -/
theorem qform_pos_of_residual {s e : ℝ} {w : ℤ → ℂ}
    (hw : MemDom w) (hw0 : w 0 = 1) (he : 0 ≤ e)
    (hmargin : e < Qform s w)
    (hres : ∀ z : ℤ → ℂ, MemDom z → z 0 = 0 →
      ‖Bform s w z‖ ^ 2 ≤ e * Qform s z)
    {u : ℤ → ℂ} (hu : MemDom u) (hne : u ≠ 0) : 0 < Qform s u := by
  by_cases hu0 : u 0 = 0
  · exact Qform_pos_of_head_zero hu hu0 (Function.ne_iff.mp hne)
  let a : ℂ := u 0
  let z : ℤ → ℂ := u - a • w
  have hz : MemDom z := by
    exact mem_Dom.mp (Dom.sub_mem (mem_Dom.mpr hu)
      (mem_Dom.mpr (memDom_smul a hw)))
  have hz0 : z 0 = 0 := by simp [z, a, hw0]
  have hqz := qform_nonneg_of_head_zero (s := s) hz hz0
  have ha : 0 < ‖a‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hu0) 2
  have hsplit : u = a • w + z := by simp [z]
  have hexp := Qform_add_expand (s := s) (memDom_smul a hw) hz
  rw [← hsplit, Qform_smul] at hexp
  have hre := congrArg Complex.re hexp
  simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at hre
  have hr : (Bform s (a • w) z).re ^ 2 ≤ ‖a‖ ^ 2 * e * Qform s z := by
    calc
      (Bform s (a • w) z).re ^ 2 ≤ ‖Bform s (a • w) z‖ ^ 2 := by
        rw [Complex.sq_norm]
        simpa only [pow_two] using Complex.re_sq_le_normSq (Bform s (a • w) z)
      _ = ‖a‖ ^ 2 * ‖Bform s w z‖ ^ 2 := by
        rw [Bform_smul_left, norm_mul, mul_pow]
        simp
      _ ≤ ‖a‖ ^ 2 * (e * Qform s z) :=
        mul_le_mul_of_nonneg_left (hres z hz hz0) ha.le
      _ = ‖a‖ ^ 2 * e * Qform s z := by ring
  have hy := residual_young he hqz ha.le hr
  have hm := mul_pos ha (sub_pos.mpr hmargin)
  nlinarith

/-- Numerical residual certificates can be consumed directly at the spectral level. -/
theorem gam_pos_of_residual {s e : ℝ} {w : ℤ → ℂ} (hs : 0 < s)
    (hw : MemDom w) (hw0 : w 0 = 1) (he : 0 ≤ e)
    (hmargin : e < Qform s w)
    (hres : ∀ z : ℤ → ℂ, MemDom z → z 0 = 0 →
      ‖Bform s w z‖ ^ 2 ≤ e * Qform s z) : 0 < gam s := by
  apply Staircase.gam_pos_of_positive_form hs
  intro u hu hn
  apply qform_pos_of_residual hw hw0 he hmargin hres hu
  intro hzero
  subst u
  simp [normSq] at hn

/-- A positive diagonal majorant for the dual residual norm. The head value
is immaterial when testing against a field whose head coefficient vanishes. -/
def residualWeight (n : ℤ) : ℝ := if n = 0 then 1 else sigP n

lemma residualWeight_pos (n : ℤ) : 0 < residualWeight n := by
  by_cases hn : n = 0
  · simp [residualWeight, hn]
  · have := sigP_ge_of_ne_zero hn
    simpa [residualWeight, hn] using (show 0 < sigP n by linarith)

lemma residualWeight_energy {s : ℝ} {z : ℤ → ℂ} (hz : MemDom z) (hzero : z 0 = 0) :
    Summable (fun n => residualWeight n * ‖z n‖ ^ 2) ∧
      (∑' n, residualWeight n * ‖z n‖ ^ 2) ≤ Qform s z := by
  have heq : (fun n => residualWeight n * ‖z n‖ ^ 2) =
      (fun n => sigP n * ‖z n‖ ^ 2) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [hzero]
    · simp [residualWeight, hn]
  rw [heq]
  refine ⟨summable_sigP_mul hz.1, ?_⟩
  have hm : 0 ≤ ∑' m, sigM m * ‖convS z m‖ ^ 2 :=
    tsum_nonneg fun m => mul_nonneg (sigM_nonneg m) (sq_nonneg _)
  have := mul_nonneg (sq_nonneg s) hm
  dsimp [Qform]
  linarith

/-- A weighted coefficient sum supplies the full residual bound, rather than
merely testing it on a finite-dimensional trial space. -/
theorem gam_pos_of_coefficient_residual {s : ℝ} {w R : ℤ → ℂ} (hs : 0 < s)
    (hw : MemDom w) (hw0 : w 0 = 1)
    (hR : Summable (fun n => ‖R n‖ ^ 2 / residualWeight n))
    (hrep : ∀ z : ℤ → ℂ, MemDom z → z 0 = 0 →
      Bform s w z = ∑' n, R n * z n)
    (hmargin : (∑' n, ‖R n‖ ^ 2 / residualWeight n) < Qform s w) :
    0 < gam s := by
  have he : 0 ≤ ∑' n, ‖R n‖ ^ 2 / residualWeight n :=
    tsum_nonneg fun n => div_nonneg (sq_nonneg _) (residualWeight_pos n).le
  apply gam_pos_of_residual hs hw hw0 he hmargin
  intro z hz hzero
  obtain ⟨hzsum, hzle⟩ := residualWeight_energy (s := s) hz hzero
  rw [hrep z hz hzero]
  exact (AlphaFourMode.weighted_complex_cauchy R z residualWeight
    residualWeight_pos hR hzsum).trans (mul_le_mul_of_nonneg_left hzle he)

end KsIndex.AlphaResidual
