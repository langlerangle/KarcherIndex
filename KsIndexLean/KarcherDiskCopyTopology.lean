module

public import KsIndexLean.KarcherFiniteDiskCopies

@[expose] public section


/-! Topology of the actual half-period disk maps and their finite quotients. -/
noncomputable section
open Set Topology
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma baseDiskPoint_isClosedEmbedding (R : PaperHalfPeriodRealization k) :
    IsClosedEmbedding R.baseDiskPoint := by
  have hs : IsClosed {q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C |
      HeightLift.height q + Real.pi ∈ Icc 0 Real.pi} :=
    isClosed_Icc.preimage (HeightLift.continuous_height.add continuous_const)
  exact hs.isClosedEmbedding_subtypeVal.comp R.diskHomeomorph.symm.isClosedEmbedding

lemma continuous_baseDiskPoint (R : PaperHalfPeriodRealization k) :
    Continuous R.baseDiskPoint := R.baseDiskPoint_isClosedEmbedding.continuous

lemma evenDiskPoint_isClosedEmbedding (R : PaperHalfPeriodRealization k) (j : ℤ) :
    IsClosedEmbedding (R.evenDiskPoint j) :=
  (HeightLift.deckHomeomorph j).isClosedEmbedding.comp R.baseDiskPoint_isClosedEmbedding

def upperDiskReflection (R : PaperHalfPeriodRealization k) :
    PeriodicEWCarrier h.out (reflectionBasepoint k) R.C ≃ₜ
      PeriodicEWCarrier h.out (reflectionBasepoint k) R.C where
  toFun := upperSeamLift R.C R.hC
  invFun := upperSeamLift R.C R.hC
  left_inv := upperSeamLift_involutive R.C R.hC
  right_inv := upperSeamLift_involutive R.C R.hC
  continuous_toFun := continuous_upperSeamLift R.C R.hC
  continuous_invFun := continuous_upperSeamLift R.C R.hC

lemma oddDiskPoint_isClosedEmbedding (R : PaperHalfPeriodRealization k) (j : ℤ) :
    IsClosedEmbedding (R.oddDiskPoint j) :=
  (HeightLift.deckHomeomorph j).isClosedEmbedding.comp
    (R.upperDiskReflection.isClosedEmbedding.comp R.baseDiskPoint_isClosedEmbedding)

lemma continuous_evenPeriodPoint (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ) :
    Continuous (R.evenPeriodPoint m j) :=
  continuous_quotient_mk'.comp (R.evenDiskPoint_isClosedEmbedding j).continuous

lemma continuous_oddPeriodPoint (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ) :
    Continuous (R.oddPeriodPoint m j) :=
  continuous_quotient_mk'.comp (R.oddDiskPoint_isClosedEmbedding j).continuous

lemma continuous_orderedDiskPoint (R : PaperHalfPeriodRealization k) {m : ℕ} [NeZero m]
    (n : ZMod (2 * m)) : Continuous (R.orderedDiskPoint n) := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · have he : R.orderedDiskPoint (evenCopyIndex j) = R.evenPeriodPoint m j.val :=
      funext (R.orderedDiskPoint_even j)
    rw [he]
    exact R.continuous_evenPeriodPoint m j.val
  · have he : R.orderedDiskPoint (oddCopyIndex j) = R.oddPeriodPoint m j.val :=
      funext (R.orderedDiskPoint_odd j)
    rw [he]
    exact R.continuous_oddPeriodPoint m j.val

lemma continuous_orderedDiskMap (R : PaperHalfPeriodRealization k) {m : ℕ} [NeZero m] :
    Continuous (fun p : ZMod (2 * m) × PuncturedClosedDisk k => R.orderedDiskPoint p.1 p.2) :=
  continuous_prod_of_discrete_left.mpr R.continuous_orderedDiskPoint

/-- The base disk map has exactly the normalized closed half-period as image. -/
lemma range_baseDiskPoint (R : PaperHalfPeriodRealization k) :
    Set.range R.baseDiskPoint =
      {q | HeightLift.height q + Real.pi ∈ Icc 0 Real.pi} := by
  ext q
  constructor
  · rintro ⟨w, rfl⟩
    exact (R.diskHomeomorph.symm w).property
  · intro hq
    exact ⟨R.diskMap ⟨q, hq⟩, R.baseDiskPoint_diskMap ⟨q, hq⟩⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
