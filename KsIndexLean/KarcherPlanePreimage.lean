module

public import KsIndexLean.KarcherPlaneDisplacement

@[expose] public section


/-! Parameter half-plane signs for the actual horizontal EW immersion. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

lemma unit_exp_arg {a : ℂ} (ha : ‖a‖ = 1) :
    Complex.exp ((a.arg : ℂ) * I) = a := by
  simpa [ha] using Complex.norm_mul_exp_arg_mul_I a

lemma unit_root_cos_arg {k : ℕ} {a : ℂ} (ha : ‖a‖ = 1)
    (hak : a ^ (2 * k) = -1) : Real.cos ((k : ℝ) * a.arg) = 0 := by
  have he : Complex.exp (((2 * (k : ℝ) * a.arg : ℝ) : ℂ) * I) = -1 := by
    calc
      _ = Complex.exp ((a.arg : ℂ)*I)^(2*k) := by
        rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
      _ = a^(2*k) := by rw [unit_exp_arg ha]
      _ = -1 := hak
  have hh := congrArg Complex.re he
  simp only [Complex.exp_ofReal_mul_I_re, Complex.neg_re, Complex.one_re] at hh
  rw [show 2 * (k : ℝ) * a.arg = 2 * ((k : ℝ)*a.arg) by ring,
    Real.cos_two_mul] at hh
  nlinarith [sq_nonneg (Real.cos ((k : ℝ)*a.arg))]

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- A point on the positive side of the parameter diameter maps to the
negative side of the corresponding ambient plane. -/
theorem plane_negative_of_parameter_im_pos
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hi : 0 < (a⁻¹ * w.val).im) :
    a.im * (centeredLiftAmbient R.C R.t q).1 +
      a.re * (centeredLiftAmbient R.C R.t q).2.1 < 0 := by
  let z : ℂ := a⁻¹*w.val
  have hz : z ≠ 0 := by intro he; have := hi; change 0 < z.im at this; simp [he] at this
  have hn : ‖z‖ = ‖w.val‖ := by simp [z, norm_inv, ha]
  have harg0 : 0 < z.arg := by
    have hh : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hi.le
    have hhne : z.arg ≠ 0 := by
      intro he
      have hs := Complex.sin_arg z
      rw [he, Real.sin_zero] at hs
      have hp : 0 < z.im / ‖z‖ := div_pos hi (norm_pos_iff.mpr hz)
      linarith
    exact lt_of_le_of_ne hh (Ne.symm hhne)
  have hargpi : z.arg < Real.pi := by
    have hh := Complex.arg_le_pi z
    have hhne : z.arg ≠ Real.pi := by
      intro he
      have hs := Complex.sin_arg z
      rw [he, Real.sin_pi] at hs
      have hp : 0 < z.im / ‖z‖ := div_pos hi (norm_pos_iff.mpr hz)
      linarith
    exact lt_of_le_of_ne hh hhne
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hwpolar : w.val = (‖z‖ : ℂ) * a * Complex.exp ((z.arg : ℂ)*I) := by
    calc
      w.val = a*z := by simp [z, ha0]
      _ = a*((‖z‖ : ℂ)*Complex.exp ((z.arg : ℂ)*I)) :=
        congrArg (fun v : ℂ => a*v) (Complex.norm_mul_exp_arg_mul_I z).symm
      _ = _ := by ring
  exact centeredLiftAmbient_plane_negative R q w hq ha hak
    (norm_pos_iff.mpr hz) (hn ▸ hw) harg0 hargpi hwpolar

/-- The sign on the opposite parameter half-plane follows by reversing
both orientations of the same plane. -/
theorem plane_positive_of_parameter_im_neg
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hi : (a⁻¹ * w.val).im < 0) :
    0 < a.im * (centeredLiftAmbient R.C R.t q).1 +
      a.re * (centeredLiftAmbient R.C R.t q).2.1 := by
  have hneg : (-a)^(2*k) = -1 := by
    rw [pow_mul, neg_sq, ← pow_mul, hak]
  have hh := R.plane_negative_of_parameter_im_pos q w hq hw
    (a := -a) (by simpa using ha) hneg (by simp only [inv_neg, neg_mul, Complex.neg_im]; linarith)
  simp only [Complex.neg_im, Complex.neg_re] at hh
  linarith

lemma plane_zero_of_nonneg_ray
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (hw : w.val = (r : ℂ) * a) :
    a.im * (centeredLiftAmbient R.C R.t q).1 +
      a.re * (centeredLiftAmbient R.C R.t q).2.1 = 0 := by
  have hh := centeredLiftAmbient_midplane_horizontal R q hr hr1
    (unit_root_cos_arg ha hak) w (by simpa [unit_exp_arg ha] using hw) hq
  have hc : Real.cos a.arg = a.re := by
    simpa using congrArg Complex.re (unit_exp_arg ha)
  have hs : Real.sin a.arg = a.im := by
    simpa using congrArg Complex.im (unit_exp_arg ha)
  rw [hh.1, hh.2, hc, hs]
  ring

/-- The parameter diameter maps into the corresponding ambient plane.
Its two unit-circle endpoints are punctures, hence absent from the carrier. -/
theorem plane_zero_of_parameter_im_zero
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hi : (a⁻¹ * w.val).im = 0) :
    a.im * (centeredLiftAmbient R.C R.t q).1 +
      a.re * (centeredLiftAmbient R.C R.t q).2.1 = 0 := by
  let s : ℝ := (a⁻¹ * w.val).re
  have hz : a⁻¹*w.val = (s : ℂ) := by
    apply Complex.ext <;> simp [s, hi]
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hws : w.val = (s : ℂ)*a := by
    calc
      _ = a*(a⁻¹ * w.val) := by simp [ha0]
      _ = _ := by rw [hz]; ring
  have hn : |s| ≤ 1 := by simpa [hws, norm_mul, ha] using hw
  have hlt : |s| < 1 := by
    apply lt_of_le_of_ne hn
    intro he
    have heq : s = 1 ∨ s = -1 := (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he
    apply w.property
    change w.val^(2*k) = -1
    rw [hws, mul_pow]
    rcases heq with hs | hs <;> simp [hs, hak]
  by_cases hs : 0 ≤ s
  · exact R.plane_zero_of_nonneg_ray q w hq ha hak hs
      (by simpa [abs_of_nonneg hs] using hlt) hws
  · have hneg : (-a)^(2*k) = -1 := by rw [pow_mul, neg_sq, ← pow_mul, hak]
    have hh := R.plane_zero_of_nonneg_ray q w hq (a := -a)
      (by simpa using ha) hneg (r := -s) (by linarith)
      (by simpa [abs_of_neg (lt_of_not_ge hs)] using hlt)
      (by rw [hws]; push_cast; ring)
    simp only [Complex.neg_im, Complex.neg_re] at hh
    linarith

/-- Exact preimage of a distinguished vertical plane on the closed
punctured parameter disk, stated without a chosen argument or polar chart. -/
theorem plane_zero_iff_parameter_im_zero
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1) :
    a.im * (centeredLiftAmbient R.C R.t q).1 +
      a.re * (centeredLiftAmbient R.C R.t q).2.1 = 0 ↔ (a⁻¹ * w.val).im = 0 := by
  constructor
  · intro hz
    rcases lt_trichotomy (a⁻¹ * w.val).im 0 with hn | he | hp
    · have hh := R.plane_positive_of_parameter_im_neg q w hq hw ha hak hn
      linarith
    · exact he
    · have hh := R.plane_negative_of_parameter_im_pos q w hq hw ha hak hp
      linarith
  · exact R.plane_zero_of_parameter_im_zero q w hq hw ha hak

/-- The paper's vertical-plane equation, with the corresponding parameter
line rotated by the inverse EW angular convention. -/
theorem vertical_plane_iff_parameter_line
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {θ : ℝ} (hθ : Real.cos ((k : ℝ) * θ) = 0) :
    (centeredLiftAmbient R.C R.t q).2.1 * Real.cos θ =
      (centeredLiftAmbient R.C R.t q).1 * Real.sin θ ↔
      (Complex.exp ((θ : ℂ)*I)*w.val).im = 0 := by
  let a : ℂ := Complex.exp (((-θ : ℝ) : ℂ)*I)
  have ha : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hak : a^(2*k) = -1 := by
    dsimp [a]
    rw [← Complex.exp_nat_mul]
    have he : (↑(2*k) : ℂ) * (((-θ : ℝ) : ℂ)*I) =
        (((2*(k : ℝ)*(-θ)) : ℝ) : ℂ)*I := by push_cast; ring
    rw [he]
    exact exp_two_mul_k_beta k (β := -θ) (by simpa using hθ)
  have hi : a⁻¹ = Complex.exp ((θ : ℂ)*I) := by
    dsimp [a]
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hh := R.plane_zero_iff_parameter_im_zero q w hq hw ha hak
  rw [hi] at hh
  have hre : a.re = Real.cos θ := by
    dsimp only [a]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : a.im = -Real.sin θ := by
    dsimp only [a]
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  rw [hre, him] at hh
  constructor
  · intro hp
    apply hh.mp
    nlinarith
  · intro hp
    have := hh.mpr hp
    nlinarith

end PaperHalfPeriodRealization
end KsIndex.KarcherData
