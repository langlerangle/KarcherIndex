module

public import KsIndexLean.KarcherCylinderCovering
public import KsIndexLean.KarcherRealConjugation

@[expose] public section


/-! Cylindrical coordinates intertwine the actual EW symmetry lifts. -/
noncomputable section
namespace KsIndex.KarcherData
open Cylindrical
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

lemma cylindricalCarrier_conjugation (q : R.CylindricalCarrier) :
    R.conjugationLift q.val ∈ R.CylindricalCarrier := by
  obtain ⟨w, hw⟩ := q.property
  refine ⟨⟨⟨(starRingEnd ℂ) w.val.val,
    (map_ne_zero (starRingEnd ℂ)).mpr w.val.property⟩,
      conjugate_not_puncture w.property⟩, ?_⟩
  rw [R.conjugationLift_projection, ← hw]
  exact (parameterConjugation_finite ⟨w.val.val, w.property⟩).symm

/-- Reflection in the vertical plane preserves time and reverses angle. -/
theorem cylindricalCover_conjugation (q : R.CylindricalCarrier) :
    (R.cylindricalCover ⟨R.conjugationLift q.val, R.cylindricalCarrier_conjugation q⟩).val =
      ((R.cylindricalCover q).val.1, (R.cylindricalCover q).val.2⁻¹) := by
  obtain ⟨w, hw⟩ := q.property
  rw [R.cylindricalCover_finite q w hw.symm]
  rw [R.cylindricalCover_finite _
    ⟨⟨(starRingEnd ℂ) w.val.val, (map_ne_zero (starRingEnd ℂ)).mpr w.val.property⟩,
      conjugate_not_puncture w.property⟩ (by
        rw [R.conjugationLift_projection, ← hw]
        exact parameterConjugation_finite ⟨w.val.val, w.property⟩)]
  exact logarithmicHomeomorph_conj w.val

lemma cylindricalCarrier_lowerSeam (q : R.CylindricalCarrier) :
    lowerSeamLift R.C R.hC q.val ∈ R.CylindricalCarrier := by
  obtain ⟨w, hw⟩ := q.property
  refine ⟨⟨⟨((starRingEnd ℂ) w.val.val)⁻¹,
    inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr w.val.property)⟩,
      inverse_conjugate_not_puncture w.property⟩, ?_⟩
  change _ = parameterSeamReflection h.out (HeightLift.projection q.val)
  rw [← hw]
  exact (parameterSeamReflection_finite h.out ⟨w.val.val, w.property⟩ w.val.property _).symm

/-- Reflection in normalized height zero reverses time and preserves angle. -/
theorem cylindricalCover_lowerSeam (q : R.CylindricalCarrier) :
    (R.cylindricalCover ⟨lowerSeamLift R.C R.hC q.val,
      R.cylindricalCarrier_lowerSeam q⟩).val =
      (-(R.cylindricalCover q).val.1, (R.cylindricalCover q).val.2) := by
  obtain ⟨w, hw⟩ := q.property
  rw [R.cylindricalCover_finite q w hw.symm]
  rw [R.cylindricalCover_finite _
    ⟨⟨((starRingEnd ℂ) w.val.val)⁻¹,
      inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr w.val.property)⟩,
      inverse_conjugate_not_puncture w.property⟩ (by
        change parameterSeamReflection h.out (HeightLift.projection q.val) = _
        rw [← hw]
        exact parameterSeamReflection_finite h.out ⟨w.val.val, w.property⟩ w.val.property _)]
  exact logarithmicHomeomorph_sigma w.val

lemma cylindricalCarrier_rotation (q : R.CylindricalCarrier) :
    R.rotationLift q.val ∈ R.CylindricalCarrier := by
  obtain ⟨w, hw⟩ := q.property
  let a := Complex.exp (((-2 * Real.pi / k : ℝ) : ℂ) * Complex.I)
  have ha : a ^ (2 * k) = 1 := by
    exact (by rw [two_mul, pow_add, paper_rotation_root h.out, one_mul])
  refine ⟨⟨⟨a * w.val.val, mul_ne_zero (Complex.exp_ne_zero _) w.val.property⟩,
    root_rotation_not_puncture ha w.property⟩, ?_⟩
  rw [R.rotationLift_projection, ← hw]
  exact (parameterRotation_finite _ _ ⟨w.val.val, w.property⟩).symm

/-- The actual rotation lift shifts the cylinder angle by −2π/k. The ambient
rotation has positive angle because `PeriodTarget.rotate a` acts by `a⁻¹`. -/
theorem cylindricalCover_rotation (q : R.CylindricalCarrier) :
    (R.cylindricalCover ⟨R.rotationLift q.val, R.cylindricalCarrier_rotation q⟩).val =
      ((R.cylindricalCover q).val.1,
        Circle.exp (-2 * Real.pi / k) * (R.cylindricalCover q).val.2) := by
  obtain ⟨w, hw⟩ := q.property
  have ha : (Complex.exp (((-2 * Real.pi / k : ℝ) : ℂ) * Complex.I)) ^ (2 * k) = 1 := by
    rw [two_mul, pow_add, paper_rotation_root h.out, one_mul]
  rw [R.cylindricalCover_finite q w hw.symm]
  rw [R.cylindricalCover_finite _
    ⟨⟨_, mul_ne_zero (Complex.exp_ne_zero _) w.val.property⟩,
      root_rotation_not_puncture ha w.property⟩ (by
        rw [R.rotationLift_projection, ← hw]
        exact parameterRotation_finite _ _ ⟨w.val.val, w.property⟩)]
  exact logarithmicHomeomorph_rotate w.val (Circle.exp (-2 * Real.pi / k))

end PaperHalfPeriodRealization
end KsIndex.KarcherData
