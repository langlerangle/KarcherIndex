module

public import KsIndexLean.KarcherSectorSeparation
public import KsIndexLean.KarcherPlaneSectors

@[expose] public section


/-! Assembly of a fundamental sector with its conjugate, and preservation of
parameter plane sides under ambient collisions. -/
noncomputable section
namespace KsIndex.KarcherData
open Complex Set
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The two sectors share their real-parameter boundary intrinsically. -/
def doubleSector (R : PaperHalfPeriodRealization k) :
    Set (PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :=
  Set.range (fun ζ => (R.heightStripPoint ζ).val) ∪
    Set.range (fun ζ => R.conjugationLift (R.heightStripPoint ζ).val)

lemma doubleSector_injective (R : PaperHalfPeriodRealization k) :
    Set.InjOn (centeredLiftAmbient R.C R.t) R.doubleSector := by
  intro q hq p hp he
  rcases hq with ⟨ζ, rfl⟩ | ⟨ζ, rfl⟩ <;>
    rcases hp with ⟨ξ, rfl⟩ | ⟨ξ, rfl⟩
  · have hh : ζ = ξ := R.isClosedEmbedding_heightStripImmersion.injective he
    rw [hh]
  · exact R.heightStrip_reflected_collision ζ ξ he
  · exact (R.heightStrip_reflected_collision ξ ζ he.symm).symm
  · have hh := congrArg (fun v : AmbientTriple => (v.1, -v.2.1, v.2.2)) he
    simp only [R.conjugationLift_ambient, neg_neg] at hh
    have hx : ζ = ξ := R.isClosedEmbedding_heightStripImmersion.injective hh
    rw [hx]

/-- An ambient collision preserves each strict parameter-plane side. This is
stronger than membership in closed checkerboard wedges. -/
lemma collision_parameter_side_pos_iff (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hp : HeightLift.projection p = finiteParameter v)
    (hw : ‖w.val‖ ≤ 1) (hv : ‖v.val‖ ≤ 1)
    {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) :
    0 < (a⁻¹ * w.val).im ↔ 0 < (a⁻¹ * v.val).im := by
  have step : ∀ (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
      (w v : PuncturedPlane k),
      HeightLift.projection q = finiteParameter w →
      HeightLift.projection p = finiteParameter v →
      ‖w.val‖ ≤ 1 → ‖v.val‖ ≤ 1 →
      centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p →
      0 < (a⁻¹ * w.val).im → 0 < (a⁻¹ * v.val).im := by
    intro q p w v hq hp hw hv he hi
    have hn := R.plane_negative_of_parameter_im_pos q w hq hw ha hak hi
    rw [he] at hn
    by_contra hh
    have hh' : (a⁻¹ * v.val).im ≤ 0 := le_of_not_gt hh
    rcases hh'.eq_or_lt with hz | hz
    · have hzero := R.plane_zero_of_parameter_im_zero p v hp hv ha hak hz
      linarith
    · have hpos := R.plane_positive_of_parameter_im_neg p v hp hv ha hak hz
      linarith
  exact ⟨step q p w v hq hp hw hv he, step p q v w hp hq hv hw he.symm⟩

lemma collision_parameter_side_nonpos_iff (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hp : HeightLift.projection p = finiteParameter v)
    (hw : ‖w.val‖ ≤ 1) (hv : ‖v.val‖ ≤ 1)
    {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) :
    (a⁻¹ * w.val).im ≤ 0 ↔ (a⁻¹ * v.val).im ≤ 0 := by
  simpa only [not_lt] using not_congr
    (R.collision_parameter_side_pos_iff q p w v hq hp hw hv ha hak he)

lemma collision_parameter_side_nonneg_iff (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C)
    (w v : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hp : HeightLift.projection p = finiteParameter v)
    (hw : ‖w.val‖ ≤ 1) (hv : ‖v.val‖ ≤ 1)
    {a : ℂ} (ha : ‖a‖ = 1) (hak : a ^ (2 * k) = -1)
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) :
    0 ≤ (a⁻¹ * w.val).im ↔ 0 ≤ (a⁻¹ * v.val).im := by
  have hneg : (-a) ^ (2 * k) = -1 := by
    rw [pow_mul, neg_sq, ← pow_mul, hak]
  simpa only [inv_neg, neg_mul, Complex.neg_im, neg_nonpos] using
    R.collision_parameter_side_nonpos_iff q p w v hq hp hw hv
      (a := -a) (by simpa using ha) hneg he

lemma heightStripPoint_range_of_sector (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hh : HeightLift.height q + Real.pi ∈ Icc 0 Real.pi)
    (hw : heightSector k w.val) :
    q ∈ Set.range (fun ζ => (R.heightStripPoint ζ).val) := by
  obtain ⟨ζ, hζ, he⟩ := heightSector_exists_strip (by have := h.out; omega : k ≠ 0) hw
  refine ⟨⟨ζ, hζ⟩, ?_⟩
  have hp := (halfPeriod_projection_isEmbedding R.C R.hC).injective
  have hsame : R.heightStripPoint ⟨ζ, hζ⟩ = (⟨q, hh⟩ : PaperHalfPeriod h.out
      (reflectionBasepoint k) R.C) := by
    apply hp
    change HeightLift.projection (R.heightStripPoint ⟨ζ, hζ⟩).val = HeightLift.projection q
    rw [R.heightStripPoint_projection, hq]
    congr 1
    exact Subtype.ext he
  exact congrArg Subtype.val hsame

/-- The doubled sector covers the full angular wedge around the positive real ray. -/
lemma mem_doubleSector_of_arg (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hh : HeightLift.height q + Real.pi ∈ Icc 0 Real.pi)
    (hw : ‖w.val‖ ≤ 1)
    (ha : -(Real.pi / (2 * k)) ≤ w.val.arg)
    (hb : w.val.arg ≤ Real.pi / (2 * k)) : q ∈ R.doubleSector := by
  by_cases hn : 0 ≤ w.val.arg
  · exact Or.inl (R.heightStripPoint_range_of_sector q w hq hh ⟨w.property, hw, hn, hb⟩)
  have harg : w.val.arg < 0 := lt_of_not_ge hn
  have he : (starRingEnd ℂ w.val).arg = -w.val.arg := by
    rw [Complex.arg_conj, ite_eq_right (by linarith [Real.pi_pos])]
  let v : PuncturedPlane k := ⟨starRingEnd ℂ w.val, conjugate_not_puncture w.property⟩
  have hv : heightSector k v.val := by
    refine ⟨v.property, ?_, ?_, ?_⟩
    · simpa [v] using hw
    · change 0 ≤ (starRingEnd ℂ w.val).arg
      rw [he]
      linarith
    · change (starRingEnd ℂ w.val).arg ≤ _
      rw [he]
      linarith
  have hp : HeightLift.projection (R.conjugationLift q) = finiteParameter v := by
    rw [R.conjugationLift_projection, hq]
    exact parameterConjugation_finite w
  obtain ⟨ζ, hζ⟩ := R.heightStripPoint_range_of_sector (R.conjugationLift q) v hp hh hv
  right
  refine ⟨ζ, ?_⟩
  change (R.heightStripPoint ζ).val = R.conjugationLift q at hζ
  change R.conjugationLift (R.heightStripPoint ζ).val = q
  exact (congrArg R.conjugationLift hζ).trans (R.conjugationLift_involutive q)

/-- Ambient injectivity on the full angular wedge, with no chosen strip witnesses
in the statement and including all boundary points. -/
lemma angular_wedge_injective (R : PaperHalfPeriodRealization k)
    (q p : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w v : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w)
    (hp : HeightLift.projection p = finiteParameter v)
    (hqz : HeightLift.height q + Real.pi ∈ Icc 0 Real.pi)
    (hpz : HeightLift.height p + Real.pi ∈ Icc 0 Real.pi)
    (hw : ‖w.val‖ ≤ 1) (hv : ‖v.val‖ ≤ 1)
    (hwa : w.val.arg ∈ Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)))
    (hva : v.val.arg ∈ Icc (-(Real.pi / (2 * k))) (Real.pi / (2 * k)))
    (he : centeredLiftAmbient R.C R.t q = centeredLiftAmbient R.C R.t p) : q = p :=
  R.doubleSector_injective (R.mem_doubleSector_of_arg q w hq hqz hw hwa.1 hwa.2)
    (R.mem_doubleSector_of_arg p v hp hpz hv hva.1 hva.2) he

end PaperHalfPeriodRealization
end KsIndex.KarcherData
