module

public import KsIndexLean.KarcherRadialDisplacement
public import KsIndexLean.KarcherCylinderCovering

@[expose] public section


/-! The only preimages of the ambient vertical axis are the two parameter poles.
The proof uses radial horizontal positivity, not global injectivity. -/
noncomputable section
namespace KsIndex.KarcherData
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The actual normalized immersion lies on the vertical axis. -/
def OnVerticalAxis (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) : Prop :=
  (centeredLiftAmbient R.C R.t q).1 = 0 ∧ (centeredLiftAmbient R.C R.t q).2.1 = 0

lemma onVerticalAxis_lowerSeam (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.OnVerticalAxis (lowerSeamLift R.C R.hC q) ↔ R.OnVerticalAxis q := by
  unfold OnVerticalAxis
  rw [centeredLiftAmbient_lowerSeam]

/-- In the closed punctured parameter disk only its center maps to the axis. -/
theorem axis_finite_disk (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (hw : ‖w.val‖ ≤ 1) (ha : R.OnVerticalAxis q) : w.val = 0 := by
  by_contra hw0
  let w0 : PuncturedPlane k := ⟨0, zero_not_puncture h.out⟩
  obtain ⟨q0, hq0⟩ := exists_halfPeriod_over_disk h.out (reflectionBasepoint k) w0 rfl R.C
    (by simp [w0])
  obtain ⟨hz1, hz2⟩ := centeredLiftAmbient_fibre_zero R q0.val hq0
  obtain ⟨h01, h02⟩ := centeredLiftAmbient_horiz_descended R q0.val w0 hq0
  obtain ⟨h1, h2⟩ := centeredLiftAmbient_horiz_descended R q w hq
  have hp := descendedIntegral_radial_positive h.out (reflectionBasepoint k) w hw hw0
  have hx : (descendedIntegral h.out (reflectionBasepoint k) w).1 =
      (descendedIntegral h.out (reflectionBasepoint k) w0).1 := by
    have := ha.1
    linarith
  have hy : (descendedIntegral h.out (reflectionBasepoint k) w).2.1 =
      (descendedIntegral h.out (reflectionBasepoint k) w0).2.1 := by
    have := ha.2
    linarith
  change 0 < w.val.re * (_ - (descendedIntegral h.out (reflectionBasepoint k) w0).1) -
    w.val.im * (_ - (descendedIntegral h.out (reflectionBasepoint k) w0).2.1) at hp
  rw [hx, hy, sub_self, sub_self] at hp
  simp at hp

/-- Exterior noncentral parameters are excluded by reflection into the disk. -/
theorem axis_finite (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w : PuncturedPlane k) (hq : HeightLift.projection q = finiteParameter w)
    (ha : R.OnVerticalAxis q) : w.val = 0 := by
  by_cases hw : ‖w.val‖ ≤ 1
  · exact R.axis_finite_disk q w hq hw ha
  · have hn : 1 < ‖w.val‖ := lt_of_not_ge hw
    have hw0 : w.val ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hn))
    let v : PuncturedPlane k := ⟨((starRingEnd ℂ) w.val)⁻¹,
      inverse_conjugate_not_puncture w.property⟩
    have hp : HeightLift.projection (lowerSeamLift R.C R.hC q) = finiteParameter v := by
      change parameterSeamReflection h.out (HeightLift.projection q) = _
      rw [hq]
      exact parameterSeamReflection_finite h.out w hw0 _
    have hv : ‖v.val‖ ≤ 1 := by
      simp only [v, norm_inv, Complex.norm_conj]
      exact inv_le_one_of_one_le₀ hn.le
    have hz := R.axis_finite_disk _ v hp hv ((R.onVerticalAxis_lowerSeam q).mpr ha)
    exact (inv_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hw0) hz).elim

/-- The regular infinity fiber also lies on the axis, by seam reflection. -/
lemma axis_infinity (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (hq : HeightLift.projection q = infinityParameter k) : R.OnVerticalAxis q := by
  apply (R.onVerticalAxis_lowerSeam q).mp
  apply centeredLiftAmbient_fibre_zero R
  change parameterSeamReflection h.out (HeightLift.projection q) = _
  rw [hq, parameterSeamReflection_infinity]

/-- Exact axis-preimage classification for the actual EW immersion. -/
theorem onVerticalAxis_iff_poles (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.OnVerticalAxis q ↔
      HeightLift.projection q = finiteParameter ⟨0, zero_not_puncture h.out⟩ ∨
        HeightLift.projection q = infinityParameter k := by
  constructor
  · intro ha
    rcases parameterSphere_cases (HeightLift.projection q) with hi | ⟨w, hw⟩
    · exact Or.inr hi
    · left
      rw [← hw]
      congr 1
      exact Subtype.ext (R.axis_finite q w hw.symm ha)
  · rintro (hz | hi)
    · exact centeredLiftAmbient_fibre_zero R q hz
    · exact R.axis_infinity q hi

/-- The logarithmic-covering domain is exactly the complement of the ambient
vertical axis in the intrinsic EW carrier. -/
theorem cylindricalCarrier_iff_not_axis
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    q ∈ R.CylindricalCarrier ↔ ¬ R.OnVerticalAxis q := by
  change HeightLift.projection q ∈ Set.range (cylindricalParameter k) ↔ _
  rw [mem_cylindricalParameter_range h.out, R.onVerticalAxis_iff_poles, not_or]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
