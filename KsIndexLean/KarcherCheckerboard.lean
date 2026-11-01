module

public import KsIndexLean.KarcherPlaneSectors
public import KsIndexLean.KarcherAxisHeights

@[expose] public section


/-! The normalized EW image in the closed central slab lies in the alternating
closed angular wedges. Radius zero is included at the boundary axis points. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set

lemma exp_plane_root {k : ℕ} {β : ℝ} (hβ : Real.cos ((k : ℝ) * β) = 0) :
    (Complex.exp ((β : ℂ) * I)) ^ (2 * k) = -1 := by
  rw [← Complex.exp_nat_mul]
  have he : (↑(2 * k) : ℂ) * ((β : ℂ) * I) =
      (((2 * (k : ℝ) * β) : ℝ) : ℂ) * I := by push_cast; ring
  rw [he]
  exact exp_two_mul_k_beta k hβ

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

def horizontalComplex (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : ℂ :=
  (centeredLiftAmbient R.C R.t q).1 + (centeredLiftAmbient R.C R.t q).2.1 * I

lemma plane_side_nonpos
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {β : ℝ} (hβ : Real.cos ((k : ℝ) * β) = 0)
    (hi : 0 ≤ (Complex.exp (((-β : ℝ) : ℂ) * I) * w.val).im) :
    (Complex.exp ((β : ℂ) * I) * R.horizontalComplex q).im ≤ 0 := by
  let a := Complex.exp ((β : ℂ) * I)
  have ha : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I β
  have hak : a ^ (2 * k) = -1 := exp_plane_root hβ
  have hai : a⁻¹ = Complex.exp (((-β : ℝ) : ℂ) * I) := by
    dsimp [a]
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have he : (a * R.horizontalComplex q).im =
      a.im * (centeredLiftAmbient R.C R.t q).1 + 
        a.re * (centeredLiftAmbient R.C R.t q).2.1 := by
    simp [horizontalComplex, Complex.mul_im, mul_comm, add_comm]
  change (a * R.horizontalComplex q).im ≤ 0
  rw [he]
  rcases hi.eq_or_lt with hh | hh
  · exact le_of_eq (R.plane_zero_of_parameter_im_zero q w hq hw ha hak (by rw [hai]; exact hh.symm))
  · exact (R.plane_negative_of_parameter_im_pos q w hq hw ha hak (by rw [hai]; exact hh)).le

lemma plane_side_nonneg
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) {β : ℝ} (hβ : Real.cos ((k : ℝ) * β) = 0)
    (hi : (Complex.exp (((-β : ℝ) : ℂ) * I) * w.val).im ≤ 0) :
    0 ≤ (Complex.exp ((β : ℂ) * I) * R.horizontalComplex q).im := by
  let a := Complex.exp ((β : ℂ) * I)
  have ha : ‖a‖ = 1 := Complex.norm_exp_ofReal_mul_I β
  have hak : a ^ (2 * k) = -1 := exp_plane_root hβ
  have hai : a⁻¹ = Complex.exp (((-β : ℝ) : ℂ) * I) := by
    dsimp [a]
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have he : (a * R.horizontalComplex q).im =
      a.im * (centeredLiftAmbient R.C R.t q).1 + 
        a.re * (centeredLiftAmbient R.C R.t q).2.1 := by
    simp [horizontalComplex, Complex.mul_im, mul_comm, add_comm]
  change 0 ≤ (a * R.horizontalComplex q).im
  rw [he]
  rcases hi.eq_or_lt with hh | hh
  · exact le_of_eq (R.plane_zero_of_parameter_im_zero q w hq hw ha hak (by rw [hai]; exact hh)).symm
  · exact (R.plane_positive_of_parameter_im_neg q w hq hw ha hak (by rw [hai]; exact hh)).le

/-- The horizontal coordinates lie in an alternating closed angular wedge,
allowing radius zero. This predicate places no restriction on the height. -/
def InCheckerboard (p : AmbientTriple) : Prop :=
  ∃ (j : ℤ) (r θ : ℝ), 0 ≤ r ∧
    (k : ℝ) * θ / Real.pi ∈ Icc (1 / 2 + 2 * (j : ℝ)) (3 / 2 + 2 * (j : ℝ)) ∧
      p.1 = r * Real.cos θ ∧ p.2.1 = r * Real.sin θ

lemma checkerboard_of_zero_horizontal {p : AmbientTriple} (hx : p.1 = 0) (hy : p.2.1 = 0) :
    InCheckerboard (k := k) p := by
  have hk : (k : ℝ) ≠ 0 := by have := h.out; exact_mod_cast (by omega : k ≠ 0)
  refine ⟨0, 0, Real.pi / (2 * k), le_rfl, ?_, by simp [hx], by simp [hy]⟩
  have he : (k : ℝ) * (Real.pi / (2 * k)) / Real.pi = 1 / 2 := by
    field_simp
  rw [he]
  norm_num

/-- The upper half of the central slab maps into the alternating wedges. -/
theorem checkerboard_nonnegative_height
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hz : HeightLift.height q + Real.pi ∈ Icc 0 (Real.pi / 2)) :
    InCheckerboard (k := k) (centeredLiftAmbient R.C R.t q) := by
  let qh : PaperHalfPeriod h.out (reflectionBasepoint k) R.C :=
    ⟨q, ⟨hz.1, by linarith [hz.2, Real.pi_pos]⟩⟩
  let w : PuncturedPlane k := (R.diskMap qh).val
  have hq : HeightLift.projection q = finiteParameter w := (R.projection_agrees qh).symm
  have hw : ‖w.val‖ ≤ 1 := (R.diskMap qh).property
  by_cases hw0 : w.val = 0
  · have hq0 : HeightLift.projection q = finiteParameter ⟨0, zero_not_puncture h.out⟩ := by
      rw [hq]
      congr 1
      exact Subtype.ext hw0
    have ha := centeredLiftAmbient_fibre_zero R q hq0
    exact checkerboard_of_zero_horizontal ha.1 ha.2
  have hcosz : 0 ≤ Real.cos (HeightLift.height q + Real.pi) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩
  have hpow : (w.val ^ k).re ≤ 0 := by
    by_contra hn
    have hh := (cos_lift_height_shift_neg_iff h.out (reflectionBasepoint k) w rfl R.C q hq).mpr
      (lt_of_not_ge hn)
    linarith
  have hcos : Real.cos ((k : ℝ) * w.val.arg) ≤ 0 := by
    have he : w.val ^ k =
        (‖w.val‖ ^ k : ℂ) * Complex.exp ((((k : ℝ) * w.val.arg : ℝ) : ℂ) * I) := by
      calc
        _ = ((‖w.val‖ : ℂ) * Complex.exp ((w.val.arg : ℂ) * I)) ^ k :=
          congrArg (fun z : ℂ => z ^ k) (Complex.norm_mul_exp_arg_mul_I w.val).symm
        _ = _ := by rw [mul_pow, ← Complex.exp_nat_mul]; congr 2; push_cast; ring
    rw [he, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at hpow
    have hp := pow_pos (norm_pos_iff.mpr hw0) k
    nlinarith
  obtain ⟨j, hjlo, hjhi⟩ := cos_nonpos_sector hcos
  let l := (1 / 2 + 2 * (j : ℝ)) * Real.pi / (k : ℝ)
  let u := (3 / 2 + 2 * (j : ℝ)) * Real.pi / (k : ℝ)
  have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k from by have := h.out; omega)
  have hkl : (k : ℝ) * l = Real.pi / 2 + (j : ℝ) * (2 * Real.pi) := by dsimp [l]; field_simp
  have hku : (k : ℝ) * u = (Real.pi + Real.pi / 2) + (j : ℝ) * (2 * Real.pi) := by
    dsimp [u]
    field_simp
    ring
  have hlβ : l ≤ w.val.arg := (div_le_iff₀ hk).mpr (by nlinarith [hjlo])
  have hβu : w.val.arg ≤ u := (le_div_iff₀ hk).mpr (by nlinarith [hjhi])
  have hlu : l < u := by nlinarith [Real.pi_pos]
  have hwidth : u - l ≤ Real.pi := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast h.out
    nlinarith [mul_nonneg (sub_nonneg.mpr hk2) Real.pi_pos.le]
  have hcl : Real.cos ((k : ℝ) * l) = 0 := by
    rw [hkl, Real.cos_add_int_mul_two_pi, Real.cos_pi_div_two]
  have hcu : Real.cos ((k : ℝ) * u) = 0 := by
    rw [hku, Real.cos_add_int_mul_two_pi, Real.cos_add, Real.cos_pi, Real.sin_pi,
      Real.cos_pi_div_two]
    ring
  have hil : 0 ≤ (Complex.exp (((-l : ℝ) : ℂ) * I) * w.val).im := by
    rw [polar_rotated_im]
    apply mul_nonneg (norm_nonneg _)
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have hiu : (Complex.exp (((-u : ℝ) : ℂ) * I) * w.val).im ≤ 0 := by
    rw [polar_rotated_im]
    apply mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
    apply Real.sin_nonpos_of_nonpos_of_neg_pi_le <;> linarith
  have hHl := R.plane_side_nonpos q w hq hw hcl hil
  have hHu := R.plane_side_nonneg q w hq hw hcu hiu
  obtain ⟨θ, hθ, he⟩ := polar_of_sector_sides (z := R.horizontalComplex q)
    (l := -u) (u := -l) (by linarith) (by simpa using hHu) (by simpa using hHl)
  refine ⟨-j - 1, ‖R.horizontalComplex q‖, θ, norm_nonneg _, ?_, ?_, ?_⟩
  · simp only [Int.cast_sub, Int.cast_neg, Int.cast_one]
    constructor
    · apply (le_div_iff₀ Real.pi_pos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hθ.1 hk.le]
    · apply (div_le_iff₀ Real.pi_pos).mpr
      nlinarith [mul_le_mul_of_nonneg_left hθ.2 hk.le]
  · have hh := congrArg Complex.re he
    simpa [horizontalComplex, Complex.mul_re, Complex.exp_ofReal_mul_I_re] using hh
  · have hh := congrArg Complex.im he
    simpa [horizontalComplex, Complex.mul_im, Complex.exp_ofReal_mul_I_im] using hh

/-- Checkerboard containment in the closed central slab. The polar radius is
nonnegative, including the two boundary axis points omitted by a strict positive-radius
formulation. -/
theorem checkerboard_closed_slab
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hz : |HeightLift.height q + Real.pi| ≤ Real.pi / 2) :
    InCheckerboard (k := k) (centeredLiftAmbient R.C R.t q) := by
  by_cases hn : 0 ≤ HeightLift.height q + Real.pi
  · exact R.checkerboard_nonnegative_height q ⟨hn, (abs_le.mp hz).2⟩
  · have hh : HeightLift.height (lowerSeamLift R.C R.hC q) + Real.pi ∈ Icc 0 (Real.pi / 2) := by
      rw [lowerSeamLift_height]
      exact ⟨by linarith, by linarith [(abs_le.mp hz).1]⟩
    have hc := R.checkerboard_nonnegative_height _ hh
    rw [centeredLiftAmbient_lowerSeam] at hc
    exact hc

/-- The EW image in the closed central slab is contained in the union of the
alternating closed polar wedges in that slab, with radius zero included. -/
theorem checkerboard_image_containment :
    Set.range (centeredLiftAmbient (k := k) R.C R.t) ∩
        {p : AmbientTriple | |p.2.2| ≤ Real.pi / 2} ⊆
      {p : AmbientTriple | ∃ (j : ℤ) (r θ z : ℝ),
        (k : ℝ) * θ / Real.pi ∈ Icc (1 / 2 + 2 * (j : ℝ)) (3 / 2 + 2 * (j : ℝ)) ∧
        0 ≤ r ∧ |z| ≤ Real.pi / 2 ∧ p = (r * Real.cos θ, r * Real.sin θ, z)} := by
  rintro p ⟨⟨q, rfl⟩, hz⟩
  obtain ⟨j, r, θ, hr, hθ, hx, hy⟩ := R.checkerboard_closed_slab q hz
  exact ⟨j, r, θ, (centeredLiftAmbient R.C R.t q).2.2, hθ, hr, hz,
    Prod.ext hx (Prod.ext hy rfl)⟩

end PaperHalfPeriodRealization
end KsIndex.KarcherData
