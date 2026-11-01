module

public import KsIndexLean.KarcherConjugationPullback

@[expose] public section


/-! Reflection in y=0 preserves each ordered half-period copy and conjugates
its disk coordinate. Function values are not conjugated. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The actual reflection restricted to the base closed half-period. -/
def halfPeriodConjugation (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    PaperHalfPeriod h.out (reflectionBasepoint k) R.C :=
  ⟨R.conjugationLift q.val, by
    rw [R.conjugationLift_height]
    exact q.property⟩

/-- Disk conjugation induced by the actual half-period identification. -/
def diskConjugation (R : PaperHalfPeriodRealization k) (w : PuncturedClosedDisk k) :
    PuncturedClosedDisk k :=
  R.diskHomeomorph (R.halfPeriodConjugation (R.diskHomeomorph.symm w))

lemma conjugationLift_baseDiskPoint (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    R.conjugationLift (R.baseDiskPoint w) = R.baseDiskPoint (R.diskConjugation w) := by
  simp only [baseDiskPoint, diskConjugation, Homeomorph.symm_apply_apply]
  rfl

lemma diskConjugation_coordinate (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    (R.diskConjugation w).val.val = starRingEnd ℂ w.val.val := by
  have hp := congrArg HeightLift.projection (R.conjugationLift_baseDiskPoint w)
  rw [R.conjugationLift_projection, R.baseDiskPoint_projection,
    R.baseDiskPoint_projection, parameterConjugation_finite] at hp
  have he := (isOpenEmbedding_finiteParameter k).injective hp
  exact (congrArg Subtype.val he).symm

lemma conjugationLift_upperSeam (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.conjugationLift (upperSeamLift R.C R.hC q) =
      upperSeamLift R.C R.hC (R.conjugationLift q) := by
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection _ = HeightLift.projection _
    simp only [conjugationLift_projection, upperSeamLift_projection]
    exact parameterConjugation_seam_commute h.out _
  · change HeightLift.height _ = HeightLift.height _
    rw [R.conjugationLift_height]
    change -HeightLift.height q = -HeightLift.height (R.conjugationLift q)
    rw [R.conjugationLift_height]

lemma conjugationLift_evenDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.conjugationLift (R.evenDiskPoint j w) = R.evenDiskPoint j (R.diskConjugation w) := by
  simp only [evenDiskPoint, conjugationLift_deck, conjugationLift_baseDiskPoint]

lemma conjugationLift_oddDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.conjugationLift (R.oddDiskPoint j w) = R.oddDiskPoint j (R.diskConjugation w) := by
  simp only [oddDiskPoint, conjugationLift_deck, conjugationLift_upperSeam, conjugationLift_baseDiskPoint]

lemma periodConjugation_evenPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodConjugation m (R.evenPeriodPoint m j w) = R.evenPeriodPoint m j (R.diskConjugation w) :=
  congrArg (HeightLift.periodQuotientMap m) (R.conjugationLift_evenDiskPoint j w)

lemma periodConjugation_oddPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodConjugation m (R.oddPeriodPoint m j w) = R.oddPeriodPoint m j (R.diskConjugation w) :=
  congrArg (HeightLift.periodQuotientMap m) (R.conjugationLift_oddDiskPoint j w)

lemma periodConjugation_orderedDiskPoint (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m] (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.periodConjugation m (R.orderedDiskPoint n w) = R.orderedDiskPoint n (R.diskConjugation w) := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    rw [← hj, orderedDiskPoint_even_int, orderedDiskPoint_even_int]
    exact R.periodConjugation_evenPoint m _ w
  · have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    rw [← hj, orderedDiskPoint_odd_int, orderedDiskPoint_odd_int]
    exact R.periodConjugation_oddPoint m _ w

end KsIndex.KarcherData.PaperHalfPeriodRealization
