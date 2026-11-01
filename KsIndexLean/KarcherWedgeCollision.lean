module

public import KsIndexLean.KarcherSectorRotation
public import KsIndexLean.KarcherCheckerboard

@[expose] public section


/-! Ambient collisions preserve a closed fundamental angular wedge. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set

lemma arg_mem_symmetric_wedge_iff {z : ℂ} {β : ℝ}
    (hb : 0 < β) (hbpi : β ≤ Real.pi / 2) :
    z.arg ∈ Icc (-β) β ↔
      0 ≤ (Complex.exp ((β : ℂ) * I) * z).im ∧
      (Complex.exp (((-β : ℝ) : ℂ) * I) * z).im ≤ 0 := by
  constructor
  · intro hz
    rw [polar_rotated_im, polar_rotated_im]
    exact ⟨mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hz.1]) (by linarith [hz.2])),
      mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hz.2]) (by linarith [hz.1]))⟩
  · rintro ⟨hl, hu⟩
    by_cases hz : z = 0
    · simp [hz, hb.le]
    obtain ⟨θ, hθ, he⟩ := polar_of_sector_sides (l := -β) (u := β)
      (by linarith) (by simpa using hl) hu
    have ht : (Complex.exp ((θ : ℂ) * I)).arg = θ := by
      have hlo : -Real.pi < ((θ : ℂ) * I).im := by
        simp only [Complex.mul_I_im, Complex.ofReal_re]
        linarith [hθ.1, Real.pi_pos]
      have hhi : ((θ : ℂ) * I).im ≤ Real.pi := by
        simp only [Complex.mul_I_im, Complex.ofReal_re]
        linarith [hθ.2, Real.pi_pos]
      have hh := congrArg Complex.im (Complex.log_exp hlo hhi)
      simpa only [Complex.log_im, Complex.mul_I_im, Complex.ofReal_re] using hh
    have hzarg : z.arg = θ := by
      conv_lhs => rw [he]
      rw [Complex.arg_real_mul _ (norm_pos_iff.mpr hz), ht]
    rwa [hzarg]

namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma collision_wedge_iff (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w v : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hp : HeightLift.projection p = finiteParameter v)
    (hw : ‖w.val‖ ≤ 1) (hv : ‖v.val‖ ≤ 1)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) :
    w.val.arg ∈ Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)) ↔
      v.val.arg ∈ Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)) := by
  let β : ℝ := Real.pi / (2 * k)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by have := h.out; omega)
  have hb : 0 < β := by dsimp [β]; positivity
  have hbpi : β ≤ Real.pi / 2 := by
    dsimp [β]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hcos : Real.cos ((k : ℝ) * β) = 0 := by
    have heq : (k : ℝ) * β = Real.pi / 2 := by dsimp [β]; field_simp
    rw [heq, Real.cos_pi_div_two]
  have hcosneg : Real.cos ((k : ℝ) * -β) = 0 := by
    rw [mul_neg, Real.cos_neg, hcos]
  have hi (θ : ℝ) : (Complex.exp ((θ : ℂ) * I))⁻¹ =
      Complex.exp (((-θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have hl := R.collision_parameter_side_nonneg_iff q p w v hq hp hw hv
    (Complex.norm_exp_ofReal_mul_I (-β)) (exp_plane_root hcosneg) he
  have hu := R.collision_parameter_side_nonpos_iff q p w v hq hp hw hv
    (Complex.norm_exp_ofReal_mul_I β) (exp_plane_root hcos) he
  rw [hi, neg_neg] at hl
  rw [hi] at hu
  change w.val.arg ∈ Icc (-β) β ↔ v.val.arg ∈ Icc (-β) β
  rw [arg_mem_symmetric_wedge_iff hb hbpi, arg_mem_symmetric_wedge_iff hb hbpi]
  exact and_congr hl hu

end PaperHalfPeriodRealization
end KsIndex.KarcherData
