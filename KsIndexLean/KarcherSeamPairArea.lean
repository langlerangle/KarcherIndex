module

public import KsIndexLean.KarcherImmersionAreaMeasure

@[expose] public section


/-! Area in the unfolded coordinates of a pair of disk interiors. This is the
measure-theoretic part of a seam chart: one side uses the disk coordinate, the
other uses circle inversion. Identifying a particular pair with an actual
seam-chart neighborhood is a separate local topological step. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology ENNReal Classical
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma ewAreaMeasure_disk_add_exterior (k : ℕ) :
    (ewAreaMeasure k).restrict Surface.disk +
      (ewAreaMeasure k).restrict {z : ℂ | 1 < ‖z‖} = ewAreaMeasure k := by
  have hd : Disjoint Surface.disk {z : ℂ | 1 < ‖z‖} := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact (lt_asymm (SurfaceForm.mem_disk_iff.mp hz) hz')
  rw [← Measure.restrict_union hd (isOpen_lt continuous_const continuous_norm).measurableSet]
  have ha : ∀ᵐ z : ℂ ∂ewAreaMeasure k, ‖z‖ ≠ 1 :=
    ae_iff.mpr (by simpa only [not_not] using (ewAreaMeasure_unitCircle_null (k := k)))
  have he : Surface.disk ∪ {z : ℂ | 1 < ‖z‖} =ᵐ[ewAreaMeasure k] Set.univ := by
    filter_upwards [ha] with z hz
    apply propext
    simp only [Set.mem_union, SurfaceForm.mem_disk_iff, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact lt_or_gt_of_ne hz
  rw [Measure.restrict_congr_set he, Measure.restrict_univ]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Coordinates for unfolding a pair; the first copy lies inside the circle. -/
def seamPairCoordinate (n : ZMod (2*m))
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) : ℂ :=
  if q ∈ R.quotientCopyInterior n then (R.diskCoordinate q).val.val
    else Bracket.σ (R.diskCoordinate q).val.val

lemma seamPairCoordinate_first (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.seamPairCoordinate n (R.orderedDiskPoint n w) = w.val.val := by
  unfold seamPairCoordinate
  rw [R.diskCoordinate_orderedDiskPoint]
  by_cases hw : ‖w.val.val‖ < 1
  · rw [ite_eq_left ((R.orderedDiskPoint_mem_copyInterior n n w).mpr ⟨rfl, hw⟩)]
  · have hn : R.orderedDiskPoint n w ∉ R.quotientCopyInterior n :=
      fun hn => hw ((R.orderedDiskPoint_mem_copyInterior n n w).mp hn).2
    rw [ite_eq_right hn]
    exact Bracket.σ_self (le_antisymm w.property (le_of_not_gt hw))

lemma seamPairCoordinate_second {n j : ZMod (2*m)} (hnj : n ≠ j)
    (w : PuncturedClosedDisk k) :
    R.seamPairCoordinate n (R.orderedDiskPoint j w) = Bracket.σ w.val.val := by
  unfold seamPairCoordinate
  rw [R.diskCoordinate_orderedDiskPoint]
  exact ite_eq_right (fun hn => hnj ((R.orderedDiskPoint_mem_copyInterior n j w).mp hn).1.symm)

lemma measurable_seamPairCoordinate (n : ZMod (2*m)) : Measurable (R.seamPairCoordinate n) := by
  exact Measurable.ite (R.isOpen_quotientCopyInterior n).measurableSet
    R.continuous_diskCoordinate_val.measurable
    (Spherical.measurable_sigma.comp R.continuous_diskCoordinate_val.measurable)

lemma map_seamPairCoordinate_first (n : ZMod (2*m)) :
    Measure.map (R.seamPairCoordinate n)
      ((R.quotientArea).restrict (R.quotientCopyInterior n)) =
      (ewAreaMeasure k).restrict Surface.disk := by
  calc
    _ = Measure.map (fun q => (R.diskCoordinate q).val.val)
        ((R.quotientArea).restrict (R.quotientCopyInterior n)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (R.isOpen_quotientCopyInterior n).measurableSet] with q hq
      exact ite_eq_left hq
    _ = _ := R.map_diskCoordinate_area_restrict n

lemma map_seamPairCoordinate_second {n j : ZMod (2*m)} (hnj : n ≠ j) :
    Measure.map (R.seamPairCoordinate n)
      ((R.quotientArea).restrict (R.quotientCopyInterior j)) =
      (ewAreaMeasure k).restrict {z : ℂ | 1 < ‖z‖} := by
  calc
    _ = Measure.map (fun q => Bracket.σ (R.diskCoordinate q).val.val)
        ((R.quotientArea).restrict (R.quotientCopyInterior j)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (R.isOpen_quotientCopyInterior j).measurableSet] with q hq
      exact ite_eq_right (fun hn => Set.disjoint_left.mp (R.quotientCopyInterior_disjoint hnj) hn hq)
    _ = _ := R.map_sigma_diskCoordinate_area_restrict j

/-- The two open sides together give full planar EW area, since the missing
circle has zero area. Distinctness is explicit, including when the chain has
only two copies. -/
lemma map_seamPairCoordinate_area {n j : ZMod (2*m)} (hnj : n ≠ j) :
    Measure.map (R.seamPairCoordinate n)
      ((R.quotientArea).restrict (R.quotientCopyInterior n ∪ R.quotientCopyInterior j)) =
      ewAreaMeasure k := by
  rw [Measure.restrict_union (R.quotientCopyInterior_disjoint hnj)
      (R.isOpen_quotientCopyInterior j).measurableSet,
    Measure.map_add _ _ (R.measurable_seamPairCoordinate n),
    R.map_seamPairCoordinate_first, R.map_seamPairCoordinate_second hnj,
    ewAreaMeasure_disk_add_exterior]

end PaperHalfPeriodRealization
end KsIndex.KarcherData
