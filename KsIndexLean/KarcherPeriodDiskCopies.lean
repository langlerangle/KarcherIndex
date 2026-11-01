module

public import KsIndexLean.KarcherDiskCopyFibers

@[expose] public section


/-! Exact disk-copy identifications after quotienting by m full EW periods. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

def evenPeriodPoint (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.mk _ (R.evenDiskPoint j w)

def oddPeriodPoint (R : PaperHalfPeriodRealization k) (m : ℕ) (j : ℤ)
    (w : PuncturedClosedDisk k) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.mk _ (R.oddDiskPoint j w)

lemma evenPeriodPoint_eq_iff (R : PaperHalfPeriodRealization k) (m : ℕ) (j l : ℤ)
    (w v : PuncturedClosedDisk k) :
    R.evenPeriodPoint m j w = R.evenPeriodPoint m l v ↔
      (j : ZMod m) = (l : ZMod m) ∧ w = v := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Quotient.exact he
    change HeightLift.deck (n * (m : ℤ)) (R.evenDiskPoint j w) = R.evenDiskPoint l v at hn
    rw [← evenDiskPoint_add] at hn
    obtain ⟨hj, hw⟩ := (R.evenDiskPoint_eq_iff _ _ _ _).mp hn
    refine ⟨?_, hw⟩
    have hc := congrArg (fun z : ℤ => (z : ZMod m)) hj
    simpa using hc
  · rintro ⟨hj, rfl⟩
    obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub j l m).mp hj
    apply Quotient.sound
    refine ⟨n, ?_⟩
    change HeightLift.deck (n * (m : ℤ)) (R.evenDiskPoint j w) = R.evenDiskPoint l w
    rw [← evenDiskPoint_add]
    congr 1
    linarith [hn]

lemma oddPeriodPoint_eq_iff (R : PaperHalfPeriodRealization k) (m : ℕ) (j l : ℤ)
    (w v : PuncturedClosedDisk k) :
    R.oddPeriodPoint m j w = R.oddPeriodPoint m l v ↔
      (j : ZMod m) = (l : ZMod m) ∧ w = v := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Quotient.exact he
    change HeightLift.deck (n * (m : ℤ)) (R.oddDiskPoint j w) = R.oddDiskPoint l v at hn
    rw [← oddDiskPoint_add] at hn
    obtain ⟨hj, hw⟩ := (R.oddDiskPoint_eq_iff _ _ _ _).mp hn
    refine ⟨?_, hw⟩
    have hc := congrArg (fun z : ℤ => (z : ZMod m)) hj
    simpa using hc
  · rintro ⟨hj, rfl⟩
    obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub j l m).mp hj
    apply Quotient.sound
    refine ⟨n, ?_⟩
    change HeightLift.deck (n * (m : ℤ)) (R.oddDiskPoint j w) = R.oddDiskPoint l w
    rw [← oddDiskPoint_add]
    congr 1
    linarith [hn]

/-- Both seam families survive also when m=1: their period indices then agree,
but the arc predicates still distinguish the two seams. -/
theorem evenPeriodPoint_eq_odd_iff (R : PaperHalfPeriodRealization k) (m : ℕ) (j l : ℤ)
    (w v : PuncturedClosedDisk k) :
    R.evenPeriodPoint m j w = R.oddPeriodPoint m l v ↔
      w = v ∧ (((j : ZMod m) = (l : ZMod m) ∧ w.val.val ∈ Surface.arc k 1) ∨
        ((j : ZMod m) = (l : ZMod m) + 1 ∧ w.val.val ∈ Surface.arc k 0)) := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Quotient.exact he
    change HeightLift.deck (n * (m : ℤ)) (R.evenDiskPoint j w) = R.oddDiskPoint l v at hn
    rw [← evenDiskPoint_add] at hn
    obtain ⟨hw, hj | hj⟩ := (R.evenDiskPoint_eq_odd_iff _ _ _ _).mp hn
    · refine ⟨hw, Or.inl ⟨?_, hj.2⟩⟩
      have hc := congrArg (fun z : ℤ => (z : ZMod m)) hj.1
      simpa using hc
    · refine ⟨hw, Or.inr ⟨?_, hj.2⟩⟩
      have hc := congrArg (fun z : ℤ => (z : ZMod m)) hj.1
      simpa using hc
  · rintro ⟨rfl, (⟨hj, ha⟩ | ⟨hj, ha⟩)⟩
    · have hs : R.evenPeriodPoint m l w = R.oddPeriodPoint m l w :=
        congrArg (Quotient.mk (HeightLift.periodSetoid m)) ((R.even_odd_seam_iff l w).mpr ha)
      exact ((R.evenPeriodPoint_eq_iff m j l w w).mpr ⟨hj, rfl⟩).trans hs
    · have hs : R.evenPeriodPoint m (l + 1) w = R.oddPeriodPoint m l w :=
        congrArg (Quotient.mk (HeightLift.periodSetoid m))
          (((R.odd_even_seam_iff l w).mpr ha).symm)
      exact ((R.evenPeriodPoint_eq_iff m j (l + 1) w w).mpr
        ⟨by simpa using hj, rfl⟩).trans hs

theorem periodDiskCopies_cover (R : PaperHalfPeriodRealization k) (m : ℕ)
    (q : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m) :
    ∃ j : ℤ, ∃ w : PuncturedClosedDisk k,
      q = R.evenPeriodPoint m j w ∨ q = R.oddPeriodPoint m j w := by
  induction q using Quotient.inductionOn with
  | h q =>
    obtain ⟨j, w, he | he⟩ := R.diskCopies_cover q
    · exact ⟨j, w, Or.inl (congrArg (Quotient.mk _) he)⟩
    · exact ⟨j, w, Or.inr (congrArg (Quotient.mk _) he)⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
