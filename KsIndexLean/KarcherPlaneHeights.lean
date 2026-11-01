module

public import KsIndexLean.KarcherPlanePreimage
public import KsIndexLean.KarcherAxisHeights

@[expose] public section


/-! Points of the EW immersion on a distinguished vertical plane have
half-integer multiples of π as their heights. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex

lemma unit_root_pow_re_zero {k : ℕ} {a : ℂ} (ha : ‖a‖ = 1)
    (hak : a ^ (2 * k) = -1) : (a ^ k).re = 0 := by
  have he : a ^ k = Complex.exp (((k : ℝ) * a.arg : ℝ) * I) := by
    calc
      a ^ k = (Complex.exp ((a.arg : ℂ) * I)) ^ k :=
        congrArg (fun z : ℂ => z ^ k) (unit_exp_arg ha).symm
      _ = _ := by rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [he, Complex.exp_ofReal_mul_I_re]
  exact unit_root_cos_arg ha hak

lemma diameter_pow_re_zero {k : ℕ} {a w : ℂ} (ha : ‖a‖ = 1)
    (hak : a ^ (2 * k) = -1) (hi : (a⁻¹ * w).im = 0) : (w ^ k).re = 0 := by
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have he : w = ((a⁻¹ * w).re : ℂ) * a := by
    have hh : a⁻¹ * w = ((a⁻¹ * w).re : ℂ) := by apply Complex.ext <;> simp [hi]
    calc
      w = a * (a⁻¹ * w) := by simp [ha0]
      _ = _ := by conv_lhs => rw [hh]
                  ring
  rw [he, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul, unit_root_pow_re_zero ha hak]
  ring

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

lemma plane_cos_height_zero_disk
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hp : a.im * (centeredLiftAmbient R.C R.t q).1
      + a.re * (centeredLiftAmbient R.C R.t q).2.1 = 0) :
    Real.cos (HeightLift.height q + Real.pi) = 0 := by
  have hi := (R.plane_zero_iff_parameter_im_zero q w hq hw ha hak).mp hp
  have hz := diameter_pow_re_zero ha hak hi
  rw [cos_lift_height_shift h.out (reflectionBasepoint k) w rfl R.C q hq,
    heightCayley_im, hz]
  simp

/-- All points on a distinguished plane, including exterior parameters and
infinity, have the asserted discrete heights. -/
theorem plane_height_half_integer
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hp : a.im * (centeredLiftAmbient R.C R.t q).1
      + a.re * (centeredLiftAmbient R.C R.t q).2.1 = 0) :
    ∃ n : ℤ, HeightLift.height q + Real.pi = ((n : ℝ) + 1 / 2) * Real.pi := by
  rcases parameterSphere_cases (HeightLift.projection q) with hi | ⟨w, hw⟩
  · exact R.axis_height_half_integer q (R.axis_infinity q hi)
  have hc : Real.cos (HeightLift.height q + Real.pi) = 0 := by
    by_cases hn : ‖w.val‖ ≤ 1
    · exact R.plane_cos_height_zero_disk q w hw.symm hn ha hak hp
    · have hn' : 1 < ‖w.val‖ := lt_of_not_ge hn
      have hw0 : w.val ≠ 0 := norm_ne_zero_iff.mp (by linarith)
      let v : PuncturedPlane k := ⟨((starRingEnd ℂ) w.val)⁻¹,
        inverse_conjugate_not_puncture w.property⟩
      have hv : ‖v.val‖ ≤ 1 := by
        simp only [v, norm_inv, Complex.norm_conj]
        exact inv_le_one_of_one_le₀ hn'.le
      have hqv : HeightLift.projection (lowerSeamLift R.C R.hC q) = finiteParameter v := by
        change parameterSeamReflection h.out (HeightLift.projection q) = _
        rw [← hw]
        exact parameterSeamReflection_finite h.out w hw0 _
      have hpv : a.im * (centeredLiftAmbient R.C R.t (lowerSeamLift R.C R.hC q)).1 + 
          a.re * (centeredLiftAmbient R.C R.t (lowerSeamLift R.C R.hC q)).2.1 = 0 := by
        rw [centeredLiftAmbient_lowerSeam]
        exact hp
      have hh := R.plane_cos_height_zero_disk _ v hqv hv ha hak hpv
      rw [lowerSeamLift_height, Real.cos_neg] at hh
      exact hh
  obtain ⟨n, hn⟩ := Real.cos_eq_zero_iff.mp hc
  exact ⟨n, by rw [hn]; ring⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
