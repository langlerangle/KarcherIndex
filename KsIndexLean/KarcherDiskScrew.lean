module

public import KsIndexLean.KarcherDiskRotation

@[expose] public section


/-! The screw exchanges consecutive disk copies and rotates their common
parameter coordinate by `exp(-πi/k)`. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Reflecting the screw image across the upper seam returns to the base half-period. -/
def halfPeriodScrewReturn (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    PaperHalfPeriod h.out (reflectionBasepoint k) R.C :=
  ⟨upperSeamLift R.C R.hC (R.screwLift q.val), by
    rw [upperSeamLift_height, R.screwLift_height]
    constructor <;> linarith [q.property.1, q.property.2]⟩

/-- Disk coordinate of the screw image, expressed in the next reflected copy. -/
def diskScrew (R : PaperHalfPeriodRealization k) (w : PuncturedClosedDisk k) :
    PuncturedClosedDisk k :=
  R.diskHomeomorph (R.halfPeriodScrewReturn (R.diskHomeomorph.symm w))

lemma screwReturn_baseDiskPoint (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    upperSeamLift R.C R.hC (R.screwLift (R.baseDiskPoint w)) =
      R.baseDiskPoint (R.diskScrew w) := by
  simp only [baseDiskPoint, diskScrew, Homeomorph.symm_apply_apply]
  rfl

lemma diskScrew_coordinate (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    (R.diskScrew w).val.val = Complex.exp ((-Real.pi / k : ℝ) * Complex.I) * w.val.val := by
  have hp := congrArg HeightLift.projection (R.screwReturn_baseDiskPoint w)
  rw [upperSeamLift_projection, R.screwLift_projection,
    R.baseDiskPoint_projection, R.baseDiskPoint_projection] at hp
  simp only [parameterScrew, Function.comp_apply] at hp
  rw [← parameterRotation_seam_commute, parameterSeamReflection_involutive,
    parameterRotation_finite] at hp
  have he := (isOpenEmbedding_finiteParameter k).injective hp
  exact (congrArg Subtype.val he).symm

lemma screwLift_baseDiskPoint (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    R.screwLift (R.baseDiskPoint w) =
      upperSeamLift R.C R.hC (R.baseDiskPoint (R.diskScrew w)) := by
  rw [← R.screwReturn_baseDiskPoint w, upperSeamLift_involutive]

lemma screwLift_deck (R : PaperHalfPeriodRealization k) (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.screwLift (HeightLift.deck j q) = HeightLift.deck j (R.screwLift q) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (HeightLift.height q + (j : ℝ) * (2 * Real.pi)) + Real.pi =
      (HeightLift.height q + Real.pi) + (j : ℝ) * (2 * Real.pi)
    ring

/-- Moving an upper reflection past the forward screw adds one whole period. -/
lemma screwLift_upperSeam (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.screwLift (upperSeamLift R.C R.hC q) =
      HeightLift.deck 1 (upperSeamLift R.C R.hC (R.screwLift q)) := by
  apply Subtype.ext
  apply Prod.ext
  · change HeightLift.projection _ = HeightLift.projection _
    simp only [screwLift_projection, upperSeamLift_projection, HeightLift.projection_deck,
      parameterScrew, Function.comp_apply]
    rw [← parameterRotation_seam_commute]
  · change -HeightLift.height q + Real.pi =
      -(HeightLift.height q + Real.pi) + ((1 : ℤ) : ℝ) * (2 * Real.pi)
    push_cast
    ring

lemma screwLift_evenDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.screwLift (R.evenDiskPoint j w) = R.oddDiskPoint j (R.diskScrew w) := by
  simp only [evenDiskPoint, oddDiskPoint, screwLift_deck, screwLift_baseDiskPoint]

lemma screwLift_oddDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.screwLift (R.oddDiskPoint j w) = R.evenDiskPoint (j + 1) (R.diskScrew w) := by
  simp only [oddDiskPoint, evenDiskPoint, screwLift_deck, screwLift_upperSeam,
    screwLift_baseDiskPoint, HeightLift.deck_add]
  rw [upperSeamLift_involutive]

end KsIndex.KarcherData.PaperHalfPeriodRealization
