module

public import KsIndexLean.KarcherCompactRegularProjection

@[expose] public section


/-! The power map between the filled end coordinates of different periods. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.DiskCompactification
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
variable (R : PaperHalfPeriodRealization k) {w : ℂ} (hw : w ∈ Surface.punctures k)

/-- Raising the root coordinate to the period number gives the one-period coordinate. -/
def endPeriodPower (t : EndRegion (m := m) hw) : EndRegion (m := 1) hw :=
  ⟨t.val ^ m, by
    change (t.val ^ m) ^ 1 * endCoordinate k w (reflectionBasepoint k).val ∈
      (endCoordinateChart h.out hw).target
    simpa only [EndRegion, filledEndRootRegion, Set.mem_ofPred_eq, pow_one] using t.property⟩

omit [NeZero m] in
lemma filledEndParameter_period_power (t : EndRegion (m := m) hw) :
    filledEndParameter h.out hw (reflectionBasepoint k) (m := 1) (endPeriodPower hw t).val =
      filledEndParameter h.out hw (reflectionBasepoint k) (m := m) t.val := by
  simp only [filledEndParameter, endPeriodPower, pow_one]

omit [NeZero m] in
lemma endPeriodPower_ne_zero {t : EndRegion (m := m) hw} (ht : t.val ≠ 0) :
    (endPeriodPower hw t).val ≠ 0 := pow_ne_zero _ ht

lemma filledEndInverse_parameter {t : EndRegion (m := m) hw} (ht : t.val ≠ 0) :
    HeightLift.quotientProjection m ((periodQuotientHomeomorph R).symm
      ⟨filledEndInverse R hw t, (filledEndInverse_mem_regular_iff R hw t).mpr ht⟩) =
    finiteParameter ⟨filledEndParameter h.out hw (reflectionBasepoint k) (m := m) t.val,
      filledEndParameter_not_mem_punctures h.out hw
        (reflectionBasepoint k) t.property ht⟩ := by
  classical
  let u : quotientEndTarget h.out hw (reflectionBasepoint k) (m := m) :=
    ⟨t.val, by
      rw [quotientEndTarget_eq h.out (NeZero.pos m) hw (reflectionBasepoint k)]
      exact ⟨t.property, ht⟩⟩
  let e := quotientEndHomeomorph h.out (NeZero.pos m) hw (reflectionBasepoint k) R.C R.hC
  let q := e.symm u
  have hfilled : (⟨filledEndInverse R hw t,
      (filledEndInverse_mem_regular_iff R hw t).mpr ht⟩ : regularSet) =
      periodQuotientHomeomorph R q.val := by
    apply Subtype.ext
    simp only [filledEndInverse, dite_eq_right ht]
    rfl
  rw [hfilled, Homeomorph.symm_apply_apply]
  obtain ⟨z,hz,hp⟩ := q.property
  have he : quotientEndRoot h.out (NeZero.pos m) (reflectionBasepoint k) w R.C q.val =
      t.val := congrArg Subtype.val (e.apply_symm_apply u)
  have ha := filledEndParameter_quotientEndRoot h.out (NeZero.pos m) hw
    (reflectionBasepoint k) R.C q.val z hz hp
  rw [he] at ha
  rw [hp]
  congr 1
  exact Subtype.ext ha.symm

lemma endPeriodPower_center :
    endPeriodPower hw (endCenter (m := m) hw) = endCenter (m := 1) hw := by
  apply Subtype.ext
  exact zero_pow (NeZero.ne m)

/-- In the actual filled end charts, period projection is the power map `t ↦ t^m`. -/
theorem compactPeriodProjection_end_power (t : EndRegion (m := m) hw) :
    compactPeriodProjection (filledEndInverse R hw t) =
      filledEndInverse R hw (endPeriodPower hw t) := by
  by_cases ht : t.val = 0
  · have he : t = endCenter hw := Subtype.ext ht
    rw [he, endPeriodPower_center, filledEndInverse_center, filledEndInverse_center,
      compactPeriodProjection_vertex]
  · let u : regularSet (k := k) (m := m) :=
      ⟨filledEndInverse R hw t, (filledEndInverse_mem_regular_iff R hw t).mpr ht⟩
    let v : regularSet (k := k) (m := 1) :=
      ⟨filledEndInverse R hw (endPeriodPower hw t),
        (filledEndInverse_mem_regular_iff R hw _).mpr (endPeriodPower_ne_zero hw ht)⟩
    suffices he : regularPeriodProjection u = v from congrArg Subtype.val he
    apply (periodQuotientHomeomorph R).symm.injective
    apply HeightLift.onePeriodProjection_bijective.1
    have hc := regularPeriodProjection_compatibility R ((periodQuotientHomeomorph R).symm u)
    rw [Homeomorph.apply_symm_apply] at hc
    rw [hc]
    change HeightLift.quotientProjection m ((periodQuotientHomeomorph R).symm u) =
      HeightLift.quotientProjection 1 ((periodQuotientHomeomorph R).symm v)
    rw [filledEndInverse_parameter R hw ht,
      filledEndInverse_parameter R hw (endPeriodPower_ne_zero hw ht)]
    congr 1
    exact Subtype.ext (filledEndParameter_period_power hw t).symm

end KsIndex.KarcherData.DiskCompactification
