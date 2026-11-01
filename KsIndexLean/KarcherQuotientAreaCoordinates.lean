module

public import KsIndexLean.KarcherQuotientAreaSeams

@[expose] public section


/-! Area in the disk coordinates of the actual EW quotient. The coordinate
map folds along the seams; its restriction to any one disk interior is
one-to-one. It is not asserted to be a chart across a seam. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology ENNReal
namespace KsIndex.KarcherData
open scoped QuotientArea
namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- The common disk coordinate of a point, independent of its copy at a seam. -/
def diskCoordinate (q : HeightLift.PeriodQuotient
    (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : PuncturedClosedDisk k :=
  (R.orderedDiskPoint_surjective q).choose.2

lemma diskCoordinate_orderedDiskPoint (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.diskCoordinate (R.orderedDiskPoint n w) = w := by
  exact ((R.orderedDiskPoint_eq_iff_gluing
    (R.orderedDiskPoint_surjective (R.orderedDiskPoint n w)).choose (n,w)).mp
      (R.orderedDiskPoint_surjective (R.orderedDiskPoint n w)).choose_spec).1

lemma continuous_diskCoordinate : Continuous (R.diskCoordinate (m := m)) := by
  apply R.orderedDiskMap_isQuotientMap.continuous_iff.mpr
  have he : R.diskCoordinate ∘ (fun p : ZMod (2*m) × PuncturedClosedDisk k =>
      R.orderedDiskPoint p.1 p.2) = Prod.snd := by
    funext p
    exact R.diskCoordinate_orderedDiskPoint p.1 p.2
  rw [he]
  exact continuous_snd

lemma continuous_diskCoordinate_val :
    Continuous (fun q => (R.diskCoordinate (m := m) q).val.val) := by
  have hc : Continuous (fun w : PuncturedClosedDisk k => w.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact hc.comp R.continuous_diskCoordinate

/-- The interior of each actual disk copy has its usual open-disk topology. -/
def copyInteriorHomeomorph (n : ZMod (2*m)) :
    {q // q ∈ R.quotientCopyInterior n} ≃ₜ {z : ℂ // ‖z‖ < 1} where
  toFun q := ⟨(R.diskCoordinate q.val).val.val, by
    obtain ⟨w, hw, he⟩ := q.property
    rw [← he, R.diskCoordinate_orderedDiskPoint]
    exact hw⟩
  invFun z := ⟨R.orderedDiskPoint n
    ⟨⟨z.val, not_puncture_of_norm_lt_one h.out z.property⟩, z.property.le⟩,
    ⟨_, z.property, rfl⟩⟩
  left_inv q := by
    apply Subtype.ext
    obtain ⟨w, hw, he⟩ := q.property
    simp only [← he, R.diskCoordinate_orderedDiskPoint]
    rfl
  right_inv z := by
    apply Subtype.ext
    change (R.diskCoordinate (R.orderedDiskPoint n _)).val.val = z.val
    exact congrArg (fun w : PuncturedClosedDisk k => w.val.val)
      (R.diskCoordinate_orderedDiskPoint n _)
  continuous_toFun := by
    exact (R.continuous_diskCoordinate_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun z : {z : ℂ // ‖z‖ < 1} =>
        (⟨⟨z.val, not_puncture_of_norm_lt_one h.out z.property⟩, z.property.le⟩ :
          PuncturedClosedDisk k)) :=
      (continuous_subtype_val.subtype_mk _).subtype_mk _
    exact ((R.continuous_orderedDiskPoint n).comp hc).subtype_mk _

/-- On one actual open disk copy, the area measure has exactly the EW planar
coordinate density. Boundaries have already been removed by a null-set proof. -/
lemma map_diskCoordinate_area_restrict (n : ZMod (2*m)) :
    Measure.map (fun q => (R.diskCoordinate q).val.val)
      ((R.quotientArea).restrict (R.quotientCopyInterior n)) =
      (ewAreaMeasure k).restrict Surface.disk := by
  rw [R.quotientArea_restrict_copyInterior n,
    Measure.map_map
      R.continuous_diskCoordinate_val.measurable
      (R.measurable_orderedDiskPoint n)]
  have he : (fun q => (R.diskCoordinate q).val.val) ∘ R.orderedDiskPoint n =
      (fun w : PuncturedClosedDisk k => w.val.val) := by
    funext w
    simp only [Function.comp_apply, R.diskCoordinate_orderedDiskPoint]
  rw [he]
  exact ewDiskMeasure_map_coe h.out

lemma lintegral_diskCoordinate_area_restrict (n : ZMod (2*m))
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q in R.quotientCopyInterior n, f (R.diskCoordinate q).val.val ∂(R.quotientArea) =
      ∫⁻ z in Surface.disk, f z ∂ewAreaMeasure k := by
  rw [← R.map_diskCoordinate_area_restrict n]
  exact (lintegral_map hf R.continuous_diskCoordinate_val.measurable).symm

end PaperHalfPeriodRealization
end KsIndex.KarcherData
