module

public import KsIndexLean.KarcherDiskCopies

@[expose] public section


/-! Every point of the actual periodic carrier lies in an ordered disk copy. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma baseDiskPoint_injective (R : PaperHalfPeriodRealization k) :
    Function.Injective R.baseDiskPoint := by
  intro w v he
  exact R.diskHomeomorph.symm.injective (Subtype.ext he)

lemma evenDiskPoint_injective (R : PaperHalfPeriodRealization k) (j : ℤ) :
    Function.Injective (R.evenDiskPoint j) :=
  (HeightLift.deckHomeomorph j).injective.comp R.baseDiskPoint_injective

lemma oddDiskPoint_injective (R : PaperHalfPeriodRealization k) (j : ℤ) :
    Function.Injective (R.oddDiskPoint j) :=
  (HeightLift.deckHomeomorph j).injective.comp
    ((upperSeamLift_involutive R.C R.hC).injective.comp R.baseDiskPoint_injective)

lemma baseDiskPoint_diskMap (R : PaperHalfPeriodRealization k)
    (q : PaperHalfPeriod h.out (reflectionBasepoint k) R.C) :
    R.baseDiskPoint (R.diskMap q) = q.val := by
  change (R.diskHomeomorph.symm (R.diskHomeomorph q)).val = q.val
  rw [Homeomorph.symm_apply_apply]

/-- Reducing the actual height modulo a full period leaves a point in the
base half-period or its upper reflection. -/
theorem diskCopies_cover (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    ∃ j : ℤ, ∃ w : PuncturedClosedDisk k,
      q = R.evenDiskPoint j w ∨ q = R.oddDiskPoint j w := by
  let x := HeightLift.height q + Real.pi
  let j : ℤ := ⌊x / (2 * Real.pi)⌋
  have hp : 0 < 2 * Real.pi := by positivity
  have hjle : (j : ℝ) * (2 * Real.pi) ≤ x :=
    (le_div_iff₀ hp).mp (Int.floor_le _)
  have hjlt : x < ((j : ℝ) + 1) * (2 * Real.pi) :=
    (div_lt_iff₀ hp).mp (Int.lt_floor_add_one _)
  let r := HeightLift.deck (-j) q
  have hr0 : 0 ≤ HeightLift.height r + Real.pi := by
    change 0 ≤ HeightLift.height q + ((-j : ℤ) : ℝ) * (2 * Real.pi) + Real.pi
    push_cast
    dsimp [x] at hjle
    linarith
  have hr2 : HeightLift.height r + Real.pi < 2 * Real.pi := by
    change HeightLift.height q + ((-j : ℤ) : ℝ) * (2 * Real.pi) + Real.pi < _
    push_cast
    dsimp [x] at hjlt
    nlinarith
  have hqr : HeightLift.deck j r = q := by
    dsimp [r]
    rw [← HeightLift.deck_add, add_neg_cancel, HeightLift.deck_zero]
  by_cases hr1 : HeightLift.height r + Real.pi ≤ Real.pi
  · let s : PaperHalfPeriod h.out (reflectionBasepoint k) R.C := ⟨r, hr0, hr1⟩
    refine ⟨j, R.diskMap s, Or.inl ?_⟩
    rw [evenDiskPoint, baseDiskPoint_diskMap]
    exact hqr.symm
  · let s : PaperHalfPeriod h.out (reflectionBasepoint k) R.C :=
      ⟨upperSeamLift R.C R.hC r, by
        rw [upperSeamLift_height]
        constructor <;> linarith⟩
    refine ⟨j, R.diskMap s, Or.inr ?_⟩
    rw [oddDiskPoint, baseDiskPoint_diskMap]
    change q = HeightLift.deck j (upperSeamLift R.C R.hC (upperSeamLift R.C R.hC r))
    rw [upperSeamLift_involutive]
    exact hqr.symm

/-- Both parity copies descend modulo m full periods. -/
lemma evenDiskPoint_period_quotient (R : PaperHalfPeriodRealization k)
    (m : ℕ) (j l : ℤ) (w : PuncturedClosedDisk k) :
    Quotient.mk (HeightLift.periodSetoid m) (R.evenDiskPoint (j + l * m) w) =
      Quotient.mk (HeightLift.periodSetoid m) (R.evenDiskPoint j w) := by
  apply Quotient.sound
  refine ⟨-l, ?_⟩
  simp only [evenDiskPoint, ← HeightLift.deck_add]
  congr 1
  ring

lemma oddDiskPoint_period_quotient (R : PaperHalfPeriodRealization k)
    (m : ℕ) (j l : ℤ) (w : PuncturedClosedDisk k) :
    Quotient.mk (HeightLift.periodSetoid m) (R.oddDiskPoint (j + l * m) w) =
      Quotient.mk (HeightLift.periodSetoid m) (R.oddDiskPoint j w) := by
  apply Quotient.sound
  refine ⟨-l, ?_⟩
  simp only [oddDiskPoint, ← HeightLift.deck_add]
  congr 1
  ring

end KsIndex.KarcherData.PaperHalfPeriodRealization
