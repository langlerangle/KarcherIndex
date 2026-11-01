module

public import KsIndexLean.KarcherDiskGluing
public import KsIndexLean.KarcherDiskCoverClosed

@[expose] public section


/-! The explicit cyclic gluing recovers the topology of the EW period quotient. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

instance gluedDiskChainTopology : TopologicalSpace (GluedDiskChain k m) :=
  inferInstanceAs (TopologicalSpace (Quotient (diskGluingSetoid k m)))

namespace PaperHalfPeriodRealization
lemma orderedDiskPoint_even_int (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint (evenCopyIndex (j : ZMod m)) w = R.evenPeriodPoint m j w := by
  rw [orderedDiskPoint_even]
  apply (R.evenPeriodPoint_eq_iff m _ _ w w).mpr
  exact ⟨by simp, rfl⟩

lemma orderedDiskPoint_odd_int (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint (oddCopyIndex (j : ZMod m)) w = R.oddPeriodPoint m j w := by
  rw [orderedDiskPoint_odd]
  apply (R.oddPeriodPoint_eq_iff m _ _ w w).mpr
  exact ⟨by simp, rfl⟩

lemma orderedDiskMap_isQuotientMap (R : PaperHalfPeriodRealization k) :
    IsQuotientMap (fun p : ZMod (2 * m) × PuncturedClosedDisk k =>
      R.orderedDiskPoint p.1 p.2) := by
  apply isQuotientMap_iff_isClosed.mpr
  refine ⟨R.orderedDiskPoint_surjective, fun A => ⟨fun hA =>
    hA.preimage R.continuous_orderedDiskMap, fun hA => ?_⟩⟩
  apply (isQuotientMap_iff_isClosed.mp (isQuotientMap_quotient_mk' (s := HeightLift.periodSetoid
    (F := extendedEWMap h.out (reflectionBasepoint k) R.C) m))).2 A |>.mpr
  apply R.isClosed_of_disk_preimages
  · intro j
    change IsClosed ((fun w => R.evenPeriodPoint m j w) ⁻¹' A)
    have hc := hA.preimage (continuous_const.prodMk continuous_id :
      Continuous (fun w : PuncturedClosedDisk k => (evenCopyIndex (j : ZMod m), w)))
    simpa only [preimage_preimage, Function.comp_def, orderedDiskPoint_even_int,
      evenPeriodPoint, Quotient.mk'] using hc
  · intro j
    change IsClosed ((fun w => R.oddPeriodPoint m j w) ⁻¹' A)
    have hc := hA.preimage (continuous_const.prodMk continuous_id :
      Continuous (fun w : PuncturedClosedDisk k => (oddCopyIndex (j : ZMod m), w)))
    simpa only [preimage_preimage, Function.comp_def, orderedDiskPoint_odd_int,
      oddPeriodPoint, Quotient.mk'] using hc

lemma gluedDiskMap_isQuotientMap (R : PaperHalfPeriodRealization k) :
    IsQuotientMap (R.gluedDiskMap (m := m)) := by
  apply isQuotientMap_quotient_mk'.of_comp_isQuotientMap
  exact R.orderedDiskMap_isQuotientMap

/-- The actual EW period quotient is homeomorphic to the explicitly glued,
cyclically ordered punctured closed disks. -/
def gluedDiskHomeomorph (R : PaperHalfPeriodRealization k) : GluedDiskChain k m ≃ₜ
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m where
  toEquiv := R.gluedDiskEquiv
  continuous_toFun := R.gluedDiskMap_isQuotientMap.continuous
  continuous_invFun := by
    apply R.gluedDiskMap_isQuotientMap.continuous_iff.mpr
    have he : (R.gluedDiskEquiv (m := m)).symm ∘ R.gluedDiskMap = id := by
      funext q
      exact (R.gluedDiskEquiv (m := m)).symm_apply_apply q
    change Continuous ((R.gluedDiskEquiv (m := m)).symm ∘ R.gluedDiskMap)
    rw [he]
    exact continuous_id

end PaperHalfPeriodRealization
end KsIndex.KarcherData
