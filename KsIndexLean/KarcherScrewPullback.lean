module

public import KsIndexLean.KarcherDiskScrew

@[expose] public section


/-! The geometric screw on finite period quotients and its ordered disk pullback. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- Positive screw action descended to the quotient by `m` full periods. -/
def periodScrew (R : PaperHalfPeriodRealization k) (m : ℕ) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m →
      HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.map R.screwLift (by
    rintro q r ⟨j, rfl⟩
    exact ⟨j, (R.screwLift_deck _ q).symm⟩)

@[simp] lemma periodScrew_mk (R : PaperHalfPeriodRealization k) (m : ℕ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) :
    R.periodScrew m (HeightLift.periodQuotientMap m q) =
      HeightLift.periodQuotientMap m (R.screwLift q) := rfl

lemma continuous_periodScrew (R : PaperHalfPeriodRealization k) (m : ℕ) :
    Continuous (R.periodScrew m) := by
  rw [(HeightLift.periodQuotientMap_isQuotientMap _).continuous_iff]
  exact (HeightLift.periodQuotientMap_isQuotientMap m).continuous.comp R.continuous_screwLift

lemma periodScrew_evenPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodScrew m (R.evenPeriodPoint m j w) = R.oddPeriodPoint m j (R.diskScrew w) :=
  congrArg (HeightLift.periodQuotientMap m) (R.screwLift_evenDiskPoint j w)

lemma periodScrew_oddPoint (R : PaperHalfPeriodRealization k) (m : ℕ)
    (j : ℤ) (w : PuncturedClosedDisk k) :
    R.periodScrew m (R.oddPeriodPoint m j w) =
      R.evenPeriodPoint m (j + 1) (R.diskScrew w) :=
  congrArg (HeightLift.periodQuotientMap m) (R.screwLift_oddDiskPoint j w)

lemma periodScrew_orderedDiskPoint (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m] (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    R.periodScrew m (R.orderedDiskPoint n w) = R.orderedDiskPoint (n + 1) (R.diskScrew w) := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · rw [evenCopyIndex_succ]
    have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    rw [← hj, orderedDiskPoint_even_int, orderedDiskPoint_odd_int]
    exact R.periodScrew_evenPoint m _ w
  · rw [oddCopyIndex_succ]
    have hj : ((j.val : ℤ) : ZMod m) = j := by simp
    have hs : (((j.val : ℤ) + 1) : ZMod m) = j+1 := by simp
    rw [← hj, orderedDiskPoint_odd_int, periodScrew_oddPoint]
    rw [hj, ← hs]
    simpa only [Int.cast_add, Int.cast_one] using
      (R.orderedDiskPoint_even_int (m := m) ((j.val : ℤ) + 1) (R.diskScrew w)).symm

/-- Forward screw pullback shifts by one disk copy and rotates the disk coordinate. -/
lemma diskFunctionPullback_screw (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ)
    (n : ZMod (2 * m)) (w : PuncturedClosedDisk k) :
    (R.diskFunctionPullback (f ∘ R.periodScrew m)).val (n, w) =
      (R.diskFunctionPullback f).val (n+1, R.diskScrew w) := by
  change f (R.periodScrew m (R.orderedDiskPoint n w)) = _
  rw [R.periodScrew_orderedDiskPoint]
  rfl

end KsIndex.KarcherData.PaperHalfPeriodRealization
