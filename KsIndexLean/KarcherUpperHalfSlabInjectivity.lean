module

public import KsIndexLean.KarcherWedgeCollision
public import KsIndexLean.KarcherWedgeRotationCoverage

@[expose] public section


/-! Global injectivity in the upper half of the fundamental height slab. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma powered_re_nonneg_of_upper_height (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hz : HeightLift.height q + Real.pi ∈ Icc (Real.pi / 2) Real.pi) :
    0 ≤ (w.val ^ k).re := by
  have hc := cos_lift_height_shift h.out (reflectionBasepoint k) w rfl R.C q hq
  have hn := norm_pos_iff.mpr (heightCayley_ne_zero w.property)
  have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hz.1
    (show HeightLift.height q + Real.pi ≤ Real.pi + Real.pi / 2 by linarith [hz.2, Real.pi_pos])
  rw [hc, div_le_iff₀ hn, zero_mul] at hcos
  have hi : 0 ≤ (heightCayley k w.val).im := by linarith
  rw [heightCayley_im,
    le_div_iff₀ (Complex.normSq_pos.mpr (height_factors_ne w.property).2), zero_mul] at hi
  linarith

/-- Rotated sector separation proves injectivity across the entire upper half-slab,
including the axis and all common sector boundaries. -/
lemma upperHalfSlab_injective (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hqz : HeightLift.height q + Real.pi ∈ Icc (Real.pi / 2) Real.pi)
    (hpz : HeightLift.height p + Real.pi ∈ Icc (Real.pi / 2) Real.pi)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) : q = p := by
  have hqhalf : HeightLift.height q + Real.pi ∈ Icc 0 Real.pi :=
    ⟨by linarith [hqz.1, Real.pi_pos], hqz.2⟩
  have hphalf : HeightLift.height p + Real.pi ∈ Icc 0 Real.pi :=
    ⟨by linarith [hpz.1, Real.pi_pos], hpz.2⟩
  let w := (R.diskMap ⟨q, hqhalf⟩).val
  let v := (R.diskMap ⟨p, hphalf⟩).val
  have hq : HeightLift.projection q = finiteParameter w := (R.projection_agrees ⟨q, hqhalf⟩).symm
  have hp : HeightLift.projection p = finiteParameter v := (R.projection_agrees ⟨p, hphalf⟩).symm
  have hw : ‖w.val‖ ≤ 1 := (R.diskMap ⟨q, hqhalf⟩).property
  have hv : ‖v.val‖ ≤ 1 := (R.diskMap ⟨p, hphalf⟩).property
  obtain ⟨n, _, hn⟩ := exists_rotation_into_wedge h.out
    (R.powered_re_nonneg_of_upper_height q w hq hqz)
  obtain ⟨w', hq', hw', hnw⟩ := R.rotationIterate_finite n q w hq
  obtain ⟨v', hp', hv', hnv⟩ := R.rotationIterate_finite n p v hp
  have he' := R.rotationIterate_collision n he
  have hw'arg : w'.val.arg ∈ Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)) := by
    rwa [hw']
  have hv'arg := (R.collision_wedge_iff _ _ w' v' hq' hp'
    (hnw.trans_le hw) (hnv.trans_le hv) he').mp hw'arg
  apply R.rotationLift_injective.iterate n
  apply R.angular_wedge_injective _ _ w' v' hq' hp' _ _
    (hnw.trans_le hw) (hnv.trans_le hv) hw'arg hv'arg he'
  · simpa only [R.rotationIterate_height] using hqhalf
  · simpa only [R.rotationIterate_height] using hphalf

end PaperHalfPeriodRealization
end KsIndex.KarcherData
