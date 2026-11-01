module

public import KsIndexLean.KarcherPlaneDifferential
public import KsIndexLean.KarcherRadialDisplacement

@[expose] public section


/-! Signed horizontal displacement relative to the vertical symmetry planes. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData
open Piecewise

/-- A radial segment in the upper parameter half-plane maps strictly to the
opposite side of the distinguished vertical plane, including a regular
unit-circle endpoint. -/
theorem descendedIntegral_plane_negative {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k)
    {r t : ℝ} {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) (htpi : t < Real.pi)
    (hwval : w.val = (r : ℂ) * a * Complex.exp ((t : ℂ) * Complex.I)) :
    a.im * ((descendedIntegral hk b w).1 -
        (descendedIntegral hk b ⟨0, zero_not_puncture hk⟩).1) +
      a.re * ((descendedIntegral hk b w).2.1 -
        (descendedIntegral hk b ⟨0, zero_not_puncture hk⟩).2.1) < 0 := by
  have hw : ‖w.val‖ ≤ 1 := by
    rw [hwval, norm_mul, norm_mul, ha, Complex.norm_exp_ofReal_mul_I,
      mul_one, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact hr1
  let p := linePiece 0 w.val
  have havoid : ∀ z ∈ Surface.punctures k, (Chain.singleton p).Avoids z := by
    intro z hz
    apply Chain.singleton_avoids
    intro t ht he
    apply radial_segment_not_puncture hk w hw ht
    have he' : (t : ℂ) * w.val = z := by simpa [p, linePiece] using he
    exact he'.symm ▸ hz
  have hc (f : ℂ → ℂ) (hf : ∀ z, z ∉ Surface.punctures k → DifferentiableAt ℂ f z) :
      ContinuousOn (fun t : ℝ => w.val * f ((t : ℂ) * w.val)) (Icc 0 1) := by
    intro t ht
    apply ContinuousWithinAt.mul continuousWithinAt_const
    have hp : Continuous (fun t : ℝ => (t : ℂ) * w.val) := by fun_prop
    exact (hf _ (radial_segment_not_puncture hk w hw ht)).continuousAt.comp_continuousWithinAt
      (f := fun s : ℝ => (s : ℂ) * w.val) hp.continuousWithinAt
  have hc1 := hc (coeff1 k) (fun _ h => differentiableAt_coeff1 h)
  have hc2 := hc (coeff2 k) (fun _ h => differentiableAt_coeff2 h)
  have hc1u : ContinuousOn (fun t : ℝ => w.val * coeff1 k ((t : ℂ)*w.val)) (uIcc 0 1) := by
    simpa using hc1
  have hc2u : ContinuousOn (fun t : ℝ => w.val * coeff2 k ((t : ℂ)*w.val)) (uIcc 0 1) := by
    simpa using hc2
  have hi1 := hc1u.intervalIntegrable (μ := volume)
  have hi2 := hc2u.intervalIntegrable (μ := volume)
  let f : ℝ → ℝ := fun u => -(a.im * (w.val * coeff1 k ((u : ℂ)*w.val)).re +
    a.re * (w.val * coeff2 k ((u : ℂ)*w.val)).re)
  have hfc : ContinuousOn f (Icc 0 1) :=
    ((continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hc1)).add
      (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hc2))).neg
  let e : ℂ := a*Complex.exp ((t : ℂ)*Complex.I)
  have hwe : w.val = (r : ℂ)*e := by simpa [e, mul_assoc] using hwval
  have hf (u : ℝ) : f u = -r *
      (a * (((ewRealDifferential k (((u*r : ℝ) : ℂ)*a*Complex.exp ((t : ℂ)*Complex.I))
        (a*Complex.exp ((t : ℂ)*Complex.I))).1 : ℂ) +
        ((ewRealDifferential k (((u*r : ℝ) : ℂ)*a*Complex.exp ((t : ℂ)*Complex.I))
          (a*Complex.exp ((t : ℂ)*Complex.I))).2.1 : ℂ)*Complex.I)).im := by
    change _ = -r * (a * (((e * coeff1 k _).re : ℂ) +
      ((e * coeff2 k _).re : ℂ)*Complex.I)).im
    have hp : (u : ℂ)*w.val = ((u*r : ℝ) : ℂ)*a*Complex.exp ((t : ℂ)*Complex.I) := by
      rw [hwval]; push_cast; ring
    dsimp [f]
    rw [hp, hwe]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  have hnon : ∀ u ∈ Ioc (0 : ℝ) 1, 0 ≤ f u := by
    intro u hu
    rw [hf]
    have hur : u*r ≤ 1 := (mul_le_of_le_one_left hr.le hu.2).trans hr1
    rcases hur.eq_or_lt with heq | hlt
    · rw [heq, Complex.ofReal_one, one_mul, ew_plane_radial_im_one hk t a ha hak]
      simp
    · exact (mul_pos_of_neg_of_neg (by linarith)
        (ew_plane_radial_im_neg hk ha hak (mul_nonneg hu.1.le hr.le) hlt ht htpi)).le
  have hpos : 0 < f 0 := by
    rw [hf, zero_mul]
    exact mul_pos_of_neg_of_neg (by linarith)
      (ew_plane_radial_im_neg hk ha hak (by norm_num) (by norm_num) ht htpi)
  have hip := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1) hfc hnon
    ⟨0, by norm_num, hpos⟩
  have hinc := descendedIntegral_increment hk b ⟨0, zero_not_puncture hk⟩ w
    (Chain.singleton p) (by simp [p]) (by simp [p]) havoid
  rw [hinc]
  simp only [quotientIntegral, periodVector, Chain.singleton_contour, projectPeriod,
    Prod.fst_add, Prod.snd_add, add_sub_cancel_left]
  have hx : (p.contour (coeff1 k)).re =
      ∫ t in (0 : ℝ)..1, (w.val * coeff1 k ((t : ℂ)*w.val)).re := by
    simpa [p, Piece.contour, linePiece] using
      (Complex.reCLM.intervalIntegral_comp_comm hi1).symm
  have hy : (p.contour (coeff2 k)).re =
      ∫ t in (0 : ℝ)..1, (w.val * coeff2 k ((t : ℂ)*w.val)).re := by
    simpa [p, Piece.contour, linePiece] using
      (Complex.reCLM.intervalIntegral_comp_comm hi2).symm
  rw [hx, hy]
  have heq : (∫ u in (0 : ℝ)..1, f u) =
      -(a.im * (∫ u in (0 : ℝ)..1, (w.val * coeff1 k ((u : ℂ)*w.val)).re) +
        a.re * (∫ u in (0 : ℝ)..1, (w.val * coeff2 k ((u : ℂ)*w.val)).re)) := by
    dsimp [f]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact (Complex.continuous_re.comp_continuousOn hc1u).intervalIntegrable.const_mul _
    · exact (Complex.continuous_re.comp_continuousOn hc2u).intervalIntegrable.const_mul _
  rw [heq] at hip
  linarith

/-- The signed plane inequality for the actual centered immersion. No
assumption of global injectivity or graphicality is used. -/
theorem centeredLiftAmbient_plane_negative {k : ℕ} [h : Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    {r t : ℝ} {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) (htpi : t < Real.pi)
    (hw : w.val = (r : ℂ) * a * Complex.exp ((t : ℂ) * Complex.I)) :
    a.im * (centeredLiftAmbient R.C R.t q).1 +
      a.re * (centeredLiftAmbient R.C R.t q).2.1 < 0 := by
  let w0 : PuncturedPlane k := ⟨0, zero_not_puncture h.out⟩
  obtain ⟨q0, hq0⟩ := exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w0 rfl R.C
    (by simp [w0])
  obtain ⟨hz1, hz2⟩ := centeredLiftAmbient_fibre_zero R q0.val hq0
  obtain ⟨h01, h02⟩ := centeredLiftAmbient_horiz_descended R q0.val w0 hq0
  obtain ⟨h1, h2⟩ := centeredLiftAmbient_horiz_descended R q w hq
  have hx : (centeredLiftAmbient R.C R.t q).1 =
      (descendedIntegral h.out (reflectionBasepoint k) w).1 -
        (descendedIntegral h.out (reflectionBasepoint k) w0).1 := by linarith
  have hy : (centeredLiftAmbient R.C R.t q).2.1 =
      (descendedIntegral h.out (reflectionBasepoint k) w).2.1 -
        (descendedIntegral h.out (reflectionBasepoint k) w0).2.1 := by linarith
  rw [hx, hy]
  exact descendedIntegral_plane_negative h.out (reflectionBasepoint k) w
    ha hak hr hr1 ht htpi hw

end KsIndex.KarcherData
