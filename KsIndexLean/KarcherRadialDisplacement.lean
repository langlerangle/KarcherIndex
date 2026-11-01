module

public import KsIndexLean.KarcherRadialPositivity

@[expose] public section


/-! Positive horizontal displacement from the central EW parameter. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.KarcherData
open Piecewise

lemma radial_segment_not_puncture {k : ℕ} (_hk : 2 ≤ k) (w : PuncturedPlane k)
    (hw : ‖w.val‖ ≤ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * w.val ∉ Surface.punctures k := by
  rcases ht.2.eq_or_lt with rfl | hlt
  · simpa using w.property
  · apply disk_not_puncture
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_right ht.1 hw) hlt

/-- A noncentral parameter in the closed disk has strictly positive horizontal
displacement in its own radial direction (with the EW angular convention). -/
theorem descendedIntegral_radial_positive {k : ℕ} (hk : 2 ≤ k) (b w : PuncturedPlane k)
    (hw : ‖w.val‖ ≤ 1) (hw0 : w.val ≠ 0) :
    0 < w.val.re * ((descendedIntegral hk b w).1 -
        (descendedIntegral hk b ⟨0, zero_not_puncture hk⟩).1) -
      w.val.im * ((descendedIntegral hk b w).2.1 -
        (descendedIntegral hk b ⟨0, zero_not_puncture hk⟩).2.1) := by
  let p := linePiece 0 w.val
  have ha : ∀ z ∈ Surface.punctures k, (Chain.singleton p).Avoids z := by
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
  let f : ℝ → ℝ := fun t => w.val.re * (w.val * coeff1 k ((t : ℂ)*w.val)).re -
    w.val.im * (w.val * coeff2 k ((t : ℂ)*w.val)).re
  have hfc : ContinuousOn f (Icc 0 1) :=
    (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hc1)).sub
      (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hc2))
  let r := ‖w.val‖
  let e : ℂ := (r : ℂ)⁻¹ * w.val
  have hr : 0 < r := norm_pos_iff.mpr hw0
  have he : ‖e‖ = 1 := by simp [e, r, norm_inv, hw0]
  have hwe : w.val = (r : ℂ) * e := by
    dsimp [e]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hr), one_mul]
  have hf (t : ℝ) : f t = r ^ 2 *
      (e * (((ewRealDifferential k (((t*r : ℝ) : ℂ)*e) e).1 : ℂ) +
        ((ewRealDifferential k (((t*r : ℝ) : ℂ)*e) e).2.1 : ℂ)*Complex.I)).re := by
    change _ = r ^ 2 * (e * (((e * coeff1 k _).re : ℂ) +
      ((e * coeff2 k _).re : ℂ)*Complex.I)).re
    have hp : (t : ℂ)*w.val = ((t*r : ℝ) : ℂ)*e := by rw [hwe]; push_cast; ring
    dsimp [f]
    rw [hp, hwe]
    simp [Complex.mul_re, Complex.mul_im, pow_two]
    ring
  have hnon : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ f t := by
    intro t ht
    rw [hf]
    exact mul_nonneg (sq_nonneg r) (ew_radial_horizontal_nonneg hk
      (mul_nonneg ht.1.le hr.le) ((mul_le_of_le_one_left hr.le ht.2).trans hw) he)
  have hpos : 0 < f 0 := by
    rw [hf, zero_mul]
    exact mul_pos (sq_pos_of_pos hr) (ew_radial_horizontal_pos hk (by norm_num) (by norm_num) he)
  have hip := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1) hfc hnon
    ⟨0, by norm_num, hpos⟩
  have hinc := descendedIntegral_increment hk b ⟨0, zero_not_puncture hk⟩ w
    (Chain.singleton p) (by simp [p]) (by simp [p]) ha
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
  have heq : (∫ t in (0 : ℝ)..1, f t) =
      w.val.re * (∫ t in (0 : ℝ)..1, (w.val * coeff1 k ((t : ℂ)*w.val)).re) -
      w.val.im * (∫ t in (0 : ℝ)..1, (w.val * coeff2 k ((t : ℂ)*w.val)).re) := by
    rw [show f = fun t : ℝ => w.val.re * (w.val * coeff1 k ((t : ℂ)*w.val)).re -
      w.val.im * (w.val * coeff2 k ((t : ℂ)*w.val)).re from rfl,
      intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · exact (Complex.continuous_re.comp_continuousOn hc1u).intervalIntegrable.const_mul _
    · exact (Complex.continuous_re.comp_continuousOn hc2u).intervalIntegrable.const_mul _
  exact heq ▸ hip

end KsIndex.KarcherData
