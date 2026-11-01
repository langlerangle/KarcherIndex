module

public import KsIndexLean.KarcherTranslationPullback

@[expose] public section


/-! Reflection in normalized height zero descends to every period quotient.
On integer-labelled copies it exchanges even j and odd (-j-1). -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma lowerSeamLift_deck (R : PaperHalfPeriodRealization k) (j : ℤ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    lowerSeamLift R.C R.hC (HeightLift.deck j q) =
      HeightLift.deck (-j) (lowerSeamLift R.C R.hC q) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change -(HeightLift.height q + (j : ℝ) * (2 * Real.pi)) +
        ((-1 : ℤ) : ℝ) * (2 * Real.pi) =
      (-HeightLift.height q + ((-1 : ℤ) : ℝ) * (2 * Real.pi)) +
        ((-j : ℤ) : ℝ) * (2 * Real.pi)
    push_cast
    ring

/-- The actual reflection in normalized height zero on the finite quotient. -/
def periodHeightReflection (R : PaperHalfPeriodRealization k) (m : ℕ) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m →
      HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.map (lowerSeamLift R.C R.hC) (by
    rintro q r ⟨j, rfl⟩
    refine ⟨-j, ?_⟩
    rw [R.lowerSeamLift_deck, neg_mul])

@[simp] lemma periodHeightReflection_mk (R : PaperHalfPeriodRealization k) (m : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.periodHeightReflection m (HeightLift.periodQuotientMap m q) =
      HeightLift.periodQuotientMap m (lowerSeamLift R.C R.hC q) := rfl

lemma continuous_periodHeightReflection (R : PaperHalfPeriodRealization k) (m : ℕ) :
    Continuous (R.periodHeightReflection m) := by
  rw [(HeightLift.periodQuotientMap_isQuotientMap _).continuous_iff]
  exact (HeightLift.periodQuotientMap_isQuotientMap m).continuous.comp
    (continuous_lowerSeamLift R.C R.hC)

lemma periodHeightReflection_involutive (R : PaperHalfPeriodRealization k) (m : ℕ) :
    Function.Involutive (R.periodHeightReflection m) := by
  intro q
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (HeightLift.periodQuotientMap m) (lowerSeamLift_involutive R.C R.hC q)

lemma periodHeightReflection_deck (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    R.periodHeightReflection m (HeightLift.periodDeck m j q) =
      HeightLift.periodDeck m (-j) (R.periodHeightReflection m q) := by
  induction q using Quotient.inductionOn with
  | h q => exact congrArg (HeightLift.periodQuotientMap m) (R.lowerSeamLift_deck j q)

lemma lowerSeamLift_evenDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    lowerSeamLift R.C R.hC (R.evenDiskPoint j w) = R.oddDiskPoint (-j-1) w := by
  rw [evenDiskPoint, R.lowerSeamLift_deck]
  simp only [lowerSeamLift, oddDiskPoint]
  rw [← HeightLift.deck_add]
  rfl

lemma lowerSeamLift_oddDiskPoint (R : PaperHalfPeriodRealization k)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    lowerSeamLift R.C R.hC (R.oddDiskPoint j w) = R.evenDiskPoint (-j-1) w := by
  rw [oddDiskPoint, R.lowerSeamLift_deck]
  change HeightLift.deck (-j) (HeightLift.deck (-1)
    (upperSeamLift R.C R.hC (upperSeamLift R.C R.hC (R.baseDiskPoint w)))) =
      HeightLift.deck (-j-1) (R.baseDiskPoint w)
  rw [upperSeamLift_involutive R.C R.hC (R.baseDiskPoint w), ← HeightLift.deck_add]
  rfl

lemma periodHeightReflection_evenPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodHeightReflection m (R.evenPeriodPoint m j w) = R.oddPeriodPoint m (-j-1) w :=
  congrArg (HeightLift.periodQuotientMap m) (R.lowerSeamLift_evenDiskPoint j w)

lemma periodHeightReflection_oddPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodHeightReflection m (R.oddPeriodPoint m j w) = R.evenPeriodPoint m (-j-1) w :=
  congrArg (HeightLift.periodQuotientMap m) (R.lowerSeamLift_oddDiskPoint j w)

end KsIndex.KarcherData.PaperHalfPeriodRealization
