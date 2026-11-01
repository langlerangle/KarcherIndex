module

public import KsIndexLean.KarcherRotationPullback

@[expose] public section


/-! Rotation preserves each ordered half-period copy and rotates its disk
coordinate by the parameter multiplier `exp(-2πi/k)`. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The actual rotation restricted to the base closed half-period. -/
def halfPeriodRotation (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    PaperHalfPeriod h.out (reflectionBasepoint k) R.C :=
  ⟨R.rotationLift q.val, by
    rw [R.rotationLift_height]
    exact q.property⟩

/-- Disk rotation induced by the actual half-period identification. -/
def diskRotation (R : PaperHalfPeriodRealization k) (w : PuncturedClosedDisk k) :
    PuncturedClosedDisk k :=
  R.diskHomeomorph (R.halfPeriodRotation (R.diskHomeomorph.symm w))

lemma rotationLift_baseDiskPoint (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    R.rotationLift (R.baseDiskPoint w) = R.baseDiskPoint (R.diskRotation w) := by
  simp only [baseDiskPoint, diskRotation, Homeomorph.symm_apply_apply]
  rfl

lemma diskRotation_coordinate (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    (R.diskRotation w).val.val = Complex.exp ((-2 * Real.pi / k : ℝ) * Complex.I) * w.val.val := by
  have hp := congrArg HeightLift.projection (R.rotationLift_baseDiskPoint w)
  rw [R.rotationLift_projection, R.baseDiskPoint_projection,
    R.baseDiskPoint_projection, parameterRotation_finite] at hp
  have he := (isOpenEmbedding_finiteParameter k).injective hp
  exact (congrArg Subtype.val he).symm

lemma rotationLift_upperSeam (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.rotationLift (upperSeamLift R.C R.hC q) =
      upperSeamLift R.C R.hC (R.rotationLift q) := by
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection _ = HeightLift.projection _
    simp only [rotationLift_projection, upperSeamLift_projection]
    exact parameterRotation_seam_commute h.out _ _ _
  · change HeightLift.height _ = HeightLift.height _
    rw [R.rotationLift_height]
    change -HeightLift.height q = -HeightLift.height (R.rotationLift q)
    rw [R.rotationLift_height]

lemma rotationLift_evenDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.rotationLift (R.evenDiskPoint j w) = R.evenDiskPoint j (R.diskRotation w) := by
  simp only [evenDiskPoint, rotationLift_deck, rotationLift_baseDiskPoint]

lemma rotationLift_oddDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.rotationLift (R.oddDiskPoint j w) = R.oddDiskPoint j (R.diskRotation w) := by
  simp only [oddDiskPoint, rotationLift_deck, rotationLift_upperSeam, rotationLift_baseDiskPoint]

lemma periodRotation_evenPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodRotation m (R.evenPeriodPoint m j w) = R.evenPeriodPoint m j (R.diskRotation w) :=
  congrArg (HeightLift.periodQuotientMap m) (R.rotationLift_evenDiskPoint j w)

lemma periodRotation_oddPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodRotation m (R.oddPeriodPoint m j w) = R.oddPeriodPoint m j (R.diskRotation w) :=
  congrArg (HeightLift.periodQuotientMap m) (R.rotationLift_oddDiskPoint j w)

lemma periodRotation_orderedDiskPoint (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m] (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.periodRotation m (R.orderedDiskPoint n w) = R.orderedDiskPoint n (R.diskRotation w) := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    rw [← hj, orderedDiskPoint_even_int, orderedDiskPoint_even_int]
    exact R.periodRotation_evenPoint m _ w
  · have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    rw [← hj, orderedDiskPoint_odd_int, orderedDiskPoint_odd_int]
    exact R.periodRotation_oddPoint m _ w

end KsIndex.KarcherData.PaperHalfPeriodRealization
