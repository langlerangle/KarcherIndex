module

public import KsIndexLean.KarcherQuotientArea
public import KsIndexLean.KarcherDiskGluingTopology

@[expose] public section


/-! The actual seam locus is closed and has zero quotient area. Exact fibers
ensure that a boundary point cannot also be an interior point of another copy. -/
noncomputable section
open Set MeasureTheory Topology
open scoped Topology ENNReal
namespace KsIndex.KarcherData
open scoped QuotientArea

lemma ewDiskMeasure_boundary_null {k : ℕ} (hk : 2 ≤ k) :
    ewDiskMeasure k {w : PuncturedClosedDisk k | ‖w.val.val‖ = 1} = 0 := by
  have hs : MeasurableSet {w : ℂ | ‖w‖ = 1} :=
    (isClosed_eq continuous_norm continuous_const).measurableSet
  have he := congrArg (fun μ : Measure ℂ => μ {w | ‖w‖ = 1}) (ewDiskMeasure_map_coe hk)
  rw [Measure.map_apply measurableEmbedding_puncturedClosedDisk_coe.measurable hs,
    Measure.restrict_apply hs] at he
  exact he.trans (measure_mono_null inter_subset_left ewAreaMeasure_unitCircle_null)

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m] (R : PaperHalfPeriodRealization k)

/-- Images of disk boundaries, with both cyclic seam families included. -/
def quotientSeams : Set
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  {q | ∃ n : ZMod (2*m), ∃ w : PuncturedClosedDisk k,
    ‖w.val.val‖ = 1 ∧ R.orderedDiskPoint n w = q}

lemma orderedDiskPoint_mem_quotientSeams (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint n w ∈ R.quotientSeams ↔ ‖w.val.val‖ = 1 := by
  constructor
  · rintro ⟨j, v, hv, he⟩
    have hvw := ((R.orderedDiskPoint_eq_iff_gluing (j,v) (n,w)).mp he).1
    change v = w at hvw
    simpa only [hvw] using hv
  · intro hw
    exact ⟨n, w, hw, rfl⟩

lemma isClosed_quotientSeams : IsClosed (R.quotientSeams (m := m)) := by
  apply (isQuotientMap_iff_isClosed.mp R.orderedDiskMap_isQuotientMap).2 _ |>.mpr
  have he : (fun p : ZMod (2*m) × PuncturedClosedDisk k => R.orderedDiskPoint p.1 p.2)
      ⁻¹' R.quotientSeams = {p | ‖p.2.val.val‖ = 1} := by
    ext p
    exact R.orderedDiskPoint_mem_quotientSeams p.1 p.2
  rw [he]
  have hc : Continuous (fun w : PuncturedClosedDisk k => w.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact isClosed_eq (continuous_norm.comp (hc.comp continuous_snd)) continuous_const

lemma quotientArea_seams_null : R.quotientArea (R.quotientSeams (m := m)) = 0 := by
  rw [quotientArea, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n _
  rw [Measure.map_apply (R.measurable_orderedDiskPoint n) R.isClosed_quotientSeams.measurableSet]
  have he : R.orderedDiskPoint n ⁻¹' R.quotientSeams =
      {w : PuncturedClosedDisk k | ‖w.val.val‖ = 1} := by
    ext w
    exact R.orderedDiskPoint_mem_quotientSeams n w
  rw [he]
  exact ewDiskMeasure_boundary_null h.out

/-- The open interior of one ordered disk in the actual quotient. -/
def quotientCopyInterior (n : ZMod (2*m)) : Set
    (HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :=
  {q | ∃ w : PuncturedClosedDisk k, ‖w.val.val‖ < 1 ∧ R.orderedDiskPoint n w = q}

lemma orderedDiskPoint_mem_copyInterior (n j : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint j w ∈ R.quotientCopyInterior n ↔ j = n ∧ ‖w.val.val‖ < 1 := by
  constructor
  · rintro ⟨v, hv, he⟩
    have hg := (R.orderedDiskPoint_eq_iff_gluing (n,v) (j,w)).mp he
    obtain ⟨hvw, hn | hn | hn⟩ := hg
    · change v = w at hvw
      exact ⟨hn.symm, hvw ▸ hv⟩
    · have heq : ‖v.val.val‖ = 1 := hn.2.1
      exact False.elim ((ne_of_lt hv) heq)
    · have heq : ‖v.val.val‖ = 1 := hn.2.1
      exact False.elim ((ne_of_lt hv) heq)
  · rintro ⟨rfl, hw⟩
    exact ⟨w, hw, rfl⟩

lemma isOpen_quotientCopyInterior (n : ZMod (2*m)) : IsOpen (R.quotientCopyInterior n) := by
  apply R.orderedDiskMap_isQuotientMap.isOpen_preimage.mp
  have he : (fun p : ZMod (2*m) × PuncturedClosedDisk k => R.orderedDiskPoint p.1 p.2)
      ⁻¹' R.quotientCopyInterior n = {p | p.1 = n} ∩ {p | ‖p.2.val.val‖ < 1} := by
    ext p
    exact R.orderedDiskPoint_mem_copyInterior n p.1 p.2
  rw [he]
  have hc : Continuous (fun w : PuncturedClosedDisk k => w.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact ((isOpen_discrete {n}).preimage continuous_fst).inter
    (isOpen_lt (continuous_norm.comp (hc.comp continuous_snd)) continuous_const)

lemma quotientCopyInterior_disjoint {n j : ZMod (2*m)} (hnj : n ≠ j) :
    Disjoint (R.quotientCopyInterior n) (R.quotientCopyInterior j) := by
  apply Set.disjoint_left.mpr
  rintro q ⟨w, hw, rfl⟩ hj
  exact hnj ((R.orderedDiskPoint_mem_copyInterior j n w).mp hj).1

lemma quotientCopyInteriors_eq_compl_seams :
    (⋃ n : ZMod (2*m), R.quotientCopyInterior n) = (R.quotientSeams (m := m))ᶜ := by
  ext q
  constructor
  · intro hq
    obtain ⟨n, w, hw, rfl⟩ := Set.mem_iUnion.mp hq
    exact fun hs => (ne_of_lt hw) ((R.orderedDiskPoint_mem_quotientSeams n w).mp hs)
  · intro hq
    obtain ⟨⟨n,w⟩, rfl⟩ := R.orderedDiskPoint_surjective q
    have hn : ‖w.val.val‖ ≠ 1 := fun hn => hq ((R.orderedDiskPoint_mem_quotientSeams n w).mpr hn)
    exact Set.mem_iUnion.mpr ⟨n, w, lt_of_le_of_ne w.property hn, rfl⟩

lemma quotientArea_restrict_copyInterior (n : ZMod (2*m)) :
    (R.quotientArea).restrict (R.quotientCopyInterior n) =
      Measure.map (R.orderedDiskPoint n) (ewDiskMeasure k) := by
  have hi : ∀ᵐ w : PuncturedClosedDisk k ∂ewDiskMeasure k, ‖w.val.val‖ < 1 := by
    have hb : ∀ᵐ w : PuncturedClosedDisk k ∂ewDiskMeasure k, ‖w.val.val‖ ≠ 1 :=
      ae_iff.mpr (by simpa only [not_not] using ewDiskMeasure_boundary_null h.out)
    filter_upwards [hb] with w hw
    exact lt_of_le_of_ne w.property hw
  apply Measure.ext
  intro A hA
  rw [Measure.restrict_apply hA, quotientArea, Measure.finsetSum_apply,
    Finset.sum_eq_single n]
  · rw [Measure.map_apply (R.measurable_orderedDiskPoint n)
      (hA.inter (R.isOpen_quotientCopyInterior n).measurableSet),
      Measure.map_apply (R.measurable_orderedDiskPoint n) hA]
    apply measure_congr
    filter_upwards [hi] with w hw
    simp only [Set.mem_preimage, Set.mem_inter_iff,
      R.orderedDiskPoint_mem_copyInterior n n w, and_self, hw, and_true]
  · intro j _ hj
    rw [Measure.map_apply (R.measurable_orderedDiskPoint j)
      (hA.inter (R.isOpen_quotientCopyInterior n).measurableSet)]
    have he : R.orderedDiskPoint j ⁻¹' (A ∩ R.quotientCopyInterior n) = ∅ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_inter_iff,
        R.orderedDiskPoint_mem_copyInterior n j w, hj, false_and, and_false, Set.mem_empty_iff_false]
    rw [he, measure_empty]
  · simp

end PaperHalfPeriodRealization
end KsIndex.KarcherData
