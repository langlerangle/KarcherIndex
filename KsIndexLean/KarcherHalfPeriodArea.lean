module

public import KsIndexLean.KarcherQuotientAreaCoordinates

@[expose] public section


/-! Area on the actual closed half-period, its coordinate law, and agreement
with the restriction of the established period-quotient area measure. -/
noncomputable section
open Set MeasureTheory Topology
namespace KsIndex.KarcherData
namespace HalfPeriodArea
scoped instance halfPeriodMeasurableSpace {k : ℕ} [h : Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) :
    MeasurableSpace (PaperHalfPeriod h.out (reflectionBasepoint k) R.C) := borel _
scoped instance halfPeriodBorelSpace {k : ℕ} [h : Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) :
    BorelSpace (PaperHalfPeriod h.out (reflectionBasepoint k) R.C) := ⟨rfl⟩
end HalfPeriodArea
open scoped QuotientArea HalfPeriodArea
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Area on the closed half-period transported by its proved disk
homeomorphism. Boundary circles are null in the source disk measure. -/
def halfPeriodArea (R : PaperHalfPeriodRealization k) :
    Measure (PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :=
  Measure.map R.diskHomeomorph.symm (ewDiskMeasure k)

lemma map_halfPeriodArea_disk (R : PaperHalfPeriodRealization k) :
    Measure.map R.diskHomeomorph R.halfPeriodArea = ewDiskMeasure k := by
  rw [halfPeriodArea,Measure.map_map R.diskHomeomorph.continuous.measurable
    R.diskHomeomorph.symm.continuous.measurable]
  have he : R.diskHomeomorph ∘ R.diskHomeomorph.symm = id :=
    funext R.diskHomeomorph.apply_symm_apply
  rw [he,Measure.map_id]

lemma map_halfPeriodArea_coordinate (R : PaperHalfPeriodRealization k) :
    Measure.map (fun q => (R.diskHomeomorph q).val.val) R.halfPeriodArea =
      (ewAreaMeasure k).restrict Surface.disk := by
  rw [← ewDiskMeasure_map_coe h.out,← R.map_halfPeriodArea_disk,
    Measure.map_map measurableEmbedding_puncturedClosedDisk_coe.measurable
      R.diskHomeomorph.continuous.measurable]
  rfl

lemma integral_halfPeriodArea_coordinate (R : PaperHalfPeriodRealization k) (F : ℂ → ℝ) :
    (∫ q, F (R.diskHomeomorph q).val.val ∂(R.halfPeriodArea)) =
      ∫ z in Surface.disk, F z ∂ewAreaMeasure k := by
  have he := (measurableEmbedding_puncturedClosedDisk_coe.comp
    R.diskHomeomorph.measurableEmbedding).integral_map (μ := R.halfPeriodArea) F
  simp only [Function.comp_def] at he
  rw [R.map_halfPeriodArea_coordinate] at he
  exact he.symm

lemma halfPeriod_quotientMap_eq (R : PaperHalfPeriodRealization k) (m : ℕ) [NeZero m]
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    HeightLift.periodQuotientMap m q.val =
      R.orderedDiskPoint (evenCopyIndex (0 : ZMod m)) (R.diskHomeomorph q) := by
  have hr := R.orderedDiskPoint_even_int (m := m) 0 (R.diskHomeomorph q)
  simp only [Int.cast_zero] at hr
  apply Eq.trans ?_ hr.symm
  change HeightLift.periodQuotientMap m q.val =
    HeightLift.periodQuotientMap m (HeightLift.deck 0
      (R.diskHomeomorph.symm (R.diskHomeomorph q)).val)
  rw [R.diskHomeomorph.symm_apply_apply,HeightLift.deck_zero]

/-- The new half-period area is the existing quotient area on its first
open copy, pushed forward by the actual period quotient map. -/
lemma map_halfPeriodArea_quotient (R : PaperHalfPeriodRealization k)
    (m : ℕ) [NeZero m] :
    Measure.map (fun q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C =>
      HeightLift.periodQuotientMap m q.val) R.halfPeriodArea =
      (R.quotientArea).restrict (R.quotientCopyInterior (evenCopyIndex (0 : ZMod m))) := by
  have he : (fun q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C =>
      HeightLift.periodQuotientMap m q.val) =
      R.orderedDiskPoint (evenCopyIndex (0 : ZMod m)) ∘ R.diskHomeomorph :=
    funext (R.halfPeriod_quotientMap_eq m)
  rw [he,← Measure.map_map (R.measurable_orderedDiskPoint _)
    R.diskHomeomorph.continuous.measurable,R.map_halfPeriodArea_disk,
    R.quotientArea_restrict_copyInterior]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
