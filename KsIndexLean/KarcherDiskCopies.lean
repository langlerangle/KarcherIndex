module

public import KsIndexLean.KarcherHalfPeriodHomeomorph

@[expose] public section


/-! Ordered closed-disk copies in the actual periodic EW carrier. Odd copies
are reflected across the upper boundary of the base half-period. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def baseDiskPoint (R : PaperHalfPeriodRealization k) (w : PuncturedClosedDisk k) :
    PeriodicEWCarrier h.out (reflectionBasepoint k) R.C :=
  (R.diskHomeomorph.symm w).val

def evenDiskPoint (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) := HeightLift.deck j (R.baseDiskPoint w)

def oddDiskPoint (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :=
  HeightLift.deck j (upperSeamLift R.C R.hC (R.baseDiskPoint w))

lemma baseDiskPoint_projection (R : PaperHalfPeriodRealization k)
    (w : PuncturedClosedDisk k) :
    HeightLift.projection (R.baseDiskPoint w) = finiteParameter w.val :=
  R.diskHomeomorph_symm_projection w

lemma evenDiskPoint_projection (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.projection (R.evenDiskPoint j w) = finiteParameter w.val :=
  R.baseDiskPoint_projection w

lemma oddDiskPoint_projection (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.projection (R.oddDiskPoint j w) =
      parameterSeamReflection h.out (finiteParameter w.val) := by
  simp only [oddDiskPoint, HeightLift.projection_deck, upperSeamLift_projection,
    baseDiskPoint_projection]

lemma evenDiskPoint_height (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.height (R.evenDiskPoint j w) + Real.pi =
      HeightLift.height (R.baseDiskPoint w) + Real.pi + (j : ℝ) * (2 * Real.pi) := by
  simp only [evenDiskPoint, HeightLift.height_deck]
  ring

lemma oddDiskPoint_height (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.height (R.oddDiskPoint j w) + Real.pi =
      2 * Real.pi - (HeightLift.height (R.baseDiskPoint w) + Real.pi) +
        (j : ℝ) * (2 * Real.pi) := by
  change -HeightLift.height (R.baseDiskPoint w) + (j : ℝ) * (2 * Real.pi) + Real.pi = _
  ring

lemma evenDiskPoint_height_mem (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.height (R.evenDiskPoint j w) + Real.pi ∈
      Set.Icc ((j : ℝ) * (2 * Real.pi)) ((j : ℝ) * (2 * Real.pi) + Real.pi) := by
  rw [evenDiskPoint_height]
  have hw := (R.diskHomeomorph.symm w).property
  change 0 ≤ HeightLift.height (R.baseDiskPoint w) + Real.pi ∧
    HeightLift.height (R.baseDiskPoint w) + Real.pi ≤ Real.pi at hw
  constructor <;> linarith [hw.1, hw.2]

lemma oddDiskPoint_height_mem (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.height (R.oddDiskPoint j w) + Real.pi ∈
      Set.Icc ((j : ℝ) * (2 * Real.pi) + Real.pi) ((j : ℝ) * (2 * Real.pi) + 2 * Real.pi) := by
  rw [oddDiskPoint_height]
  have hw := (R.diskHomeomorph.symm w).property
  change 0 ≤ HeightLift.height (R.baseDiskPoint w) + Real.pi ∧
    HeightLift.height (R.baseDiskPoint w) + Real.pi ≤ Real.pi at hw
  constructor <;> linarith [hw.1, hw.2]

lemma evenDiskPoint_add (R : PaperHalfPeriodRealization k) (j l : ℤ)
    (w : PuncturedClosedDisk k) :
    R.evenDiskPoint (j + l) w = HeightLift.deck j (R.evenDiskPoint l w) :=
  HeightLift.deck_add j l _

lemma oddDiskPoint_add (R : PaperHalfPeriodRealization k) (j l : ℤ)
    (w : PuncturedClosedDisk k) :
    R.oddDiskPoint (j + l) w = HeightLift.deck j (R.oddDiskPoint l w) :=
  HeightLift.deck_add j l _

lemma even_odd_seam_iff (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    R.evenDiskPoint j w = R.oddDiskPoint j w ↔ w.val.val ∈ Surface.arc k 1 := by
  have hi : Function.Injective (HeightLift.deck (F := extendedEWMap h.out (reflectionBasepoint k) R.C) j) :=
    (HeightLift.deckHomeomorph j).injective
  change HeightLift.deck j (R.baseDiskPoint w) =
    HeightLift.deck j (upperSeamLift R.C R.hC (R.baseDiskPoint w)) ↔ _
  rw [hi.eq_iff, eq_comm, upperSeamLift_fixed_iff]
  exact halfPeriod_height_pi_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)

lemma odd_even_seam_iff (R : PaperHalfPeriodRealization k) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    R.oddDiskPoint j w = R.evenDiskPoint (j + 1) w ↔ w.val.val ∈ Surface.arc k 0 := by
  have hi : Function.Injective (HeightLift.deck (F := extendedEWMap h.out (reflectionBasepoint k) R.C) j) :=
    (HeightLift.deckHomeomorph j).injective
  change HeightLift.deck j (upperSeamLift R.C R.hC (R.baseDiskPoint w)) =
    HeightLift.deck (j + 1) (R.baseDiskPoint w) ↔ _
  rw [HeightLift.deck_add, hi.eq_iff]
  have he : upperSeamLift R.C R.hC (R.baseDiskPoint w) = HeightLift.deck 1 (R.baseDiskPoint w) ↔
      lowerSeamLift R.C R.hC (R.baseDiskPoint w) = R.baseDiskPoint w := by
    constructor
    · intro hh
      simp only [lowerSeamLift, hh, ← HeightLift.deck_add]
      norm_num
    · intro hh
      have ht := congrArg (HeightLift.deck 1) hh
      simpa only [lowerSeamLift, ← HeightLift.deck_add, add_neg_cancel,
        HeightLift.deck_zero] using ht
  rw [he, lowerSeamLift_fixed_iff]
  exact halfPeriod_height_zero_iff_arc h.out (reflectionBasepoint k) w.val rfl R.C
    (R.diskHomeomorph.symm w) (R.baseDiskPoint_projection w)

end KsIndex.KarcherData.PaperHalfPeriodRealization
