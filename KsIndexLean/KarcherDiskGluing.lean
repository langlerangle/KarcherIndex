module

public import KsIndexLean.KarcherOrderedSeams
public import KsIndexLean.KarcherDiskCopyTopology

@[expose] public section


/-! The explicit cyclic disk gluing has exactly the fibers of the actual EW
period quotient. Both orientations of adjacency are retained, including m=1. -/
noncomputable section
namespace KsIndex.KarcherData
open PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]

def diskGluingRel (p q : ZMod (2 * m) × PuncturedClosedDisk k) : Prop :=
  p.2 = q.2 ∧ (p.1 = q.1 ∨
    (q.1 = p.1 + 1 ∧ p.2.val.val ∈ Surface.seamArc k m p.1) ∨
    (p.1 = q.1 + 1 ∧ p.2.val.val ∈ Surface.seamArc k m q.1))

omit h [NeZero m] in
lemma diskGluingRel_symm {p q : ZMod (2 * m) × PuncturedClosedDisk k}
    (hpq : diskGluingRel p q) : diskGluingRel q p := by
  obtain ⟨hw, he | he | he⟩ := hpq
  · exact ⟨hw.symm, Or.inl he.symm⟩
  · exact ⟨hw.symm, Or.inr (Or.inr ⟨he.1, hw ▸ he.2⟩)⟩
  · exact ⟨hw.symm, Or.inr (Or.inl ⟨he.1, hw ▸ he.2⟩)⟩

namespace PaperHalfPeriodRealization

private lemma even_odd_gluing (R : PaperHalfPeriodRealization k) (j l : ZMod m)
    (w v : PuncturedClosedDisk k)
    (he : R.orderedDiskPoint (evenCopyIndex j) w = R.orderedDiskPoint (oddCopyIndex l) v) :
    diskGluingRel (evenCopyIndex j, w) (oddCopyIndex l, v) := by
  rw [orderedDiskPoint_even, orderedDiskPoint_odd] at he
  have hf := (R.evenPeriodPoint_eq_odd_iff m _ _ w v).mp he
  have hc : w = v ∧ ((j = l ∧ w.val.val ∈ Surface.arc k 1) ∨
      (j = l + 1 ∧ w.val.val ∈ Surface.arc k 0)) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hf
  obtain ⟨hw, ⟨hj, ha⟩ | ⟨hj, ha⟩⟩ := hc
  · refine ⟨hw, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
    · rw [hj, evenCopyIndex_succ]
    · simpa only [seamArc_evenCopyIndex] using ha
  · refine ⟨hw, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · rw [hj, oddCopyIndex_succ]
    · simpa only [seamArc_oddCopyIndex] using ha

theorem orderedDiskPoint_eq_iff_gluing (R : PaperHalfPeriodRealization k)
    (p q : ZMod (2 * m) × PuncturedClosedDisk k) :
    R.orderedDiskPoint p.1 p.2 = R.orderedDiskPoint q.1 q.2 ↔ diskGluingRel p q := by
  rcases p with ⟨n, w⟩
  rcases q with ⟨o, v⟩
  constructor
  · intro he
    obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n <;>
      obtain ⟨l, rfl | rfl⟩ := copyIndex_cases o
    · change R.orderedDiskPoint (evenCopyIndex j) w = R.orderedDiskPoint (evenCopyIndex l) v at he
      rw [orderedDiskPoint_even, orderedDiskPoint_even] at he
      have hf := (R.evenPeriodPoint_eq_iff m _ _ w v).mp he
      have hc : j = l ∧ w = v := by
        simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hf
      exact ⟨hc.2, Or.inl (congrArg evenCopyIndex hc.1)⟩
    · exact even_odd_gluing R j l w v he
    · exact diskGluingRel_symm (even_odd_gluing R l j v w he.symm)
    · change R.orderedDiskPoint (oddCopyIndex j) w = R.orderedDiskPoint (oddCopyIndex l) v at he
      rw [orderedDiskPoint_odd, orderedDiskPoint_odd] at he
      have hf := (R.oddPeriodPoint_eq_iff m _ _ w v).mp he
      have hc : j = l ∧ w = v := by
        simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hf
      exact ⟨hc.2, Or.inl (congrArg oddCopyIndex hc.1)⟩
  · rintro ⟨hw, he | he | he⟩
    · dsimp only at hw he
      change R.orderedDiskPoint n w = R.orderedDiskPoint o v
      rw [hw, he]
    · dsimp only at hw he
      change R.orderedDiskPoint n w = R.orderedDiskPoint o v
      rw [← hw, he.1]
      exact R.orderedDiskPoint_glues n w he.2
    · dsimp only at hw he
      change R.orderedDiskPoint n w = R.orderedDiskPoint o v
      rw [← hw, he.1]
      exact (R.orderedDiskPoint_glues o w he.2).symm

end PaperHalfPeriodRealization

/-- The relation itself is specified by model copy order and arcs. The proved
EW realization certifies its equivalence laws; it is not defined as a map kernel. -/
def diskGluingSetoid (k m : ℕ) [Fact (2 ≤ k)] [NeZero m] :
    Setoid (ZMod (2 * m) × PuncturedClosedDisk k) where
  r := diskGluingRel
  iseqv := by
    let R := Classical.choice (exists_paperHalfPeriodRealization (k := k))
    have he := R.orderedDiskPoint_eq_iff_gluing (m := m)
    exact ⟨fun p => (he p p).mp rfl,
      fun hpq => diskGluingRel_symm hpq,
      fun {p q r} hpq hqr => (he p r).mp (((he p q).mpr hpq).trans ((he q r).mpr hqr))⟩

def GluedDiskChain (k m : ℕ) [Fact (2 ≤ k)] [NeZero m] := Quotient (diskGluingSetoid k m)

namespace PaperHalfPeriodRealization

def gluedDiskMap (R : PaperHalfPeriodRealization k) : GluedDiskChain k m →
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Quotient.lift (fun p => R.orderedDiskPoint p.1 p.2)
    (fun p q hpq => (R.orderedDiskPoint_eq_iff_gluing p q).mpr hpq)

theorem gluedDiskMap_bijective (R : PaperHalfPeriodRealization k) :
    Function.Bijective (R.gluedDiskMap (m := m)) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with | h p =>
      induction q using Quotient.inductionOn with | h q =>
        intro he
        exact Quotient.sound ((R.orderedDiskPoint_eq_iff_gluing p q).mp he)
  · intro q
    obtain ⟨p, hp⟩ := R.orderedDiskPoint_surjective q
    exact ⟨Quotient.mk _ p, hp⟩

/-- Set-level identification with the explicitly glued disks. Continuity of
the inverse, and therefore the homeomorphism, is a separate obligation. -/
def gluedDiskEquiv (R : PaperHalfPeriodRealization k) : GluedDiskChain k m ≃
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  Equiv.ofBijective R.gluedDiskMap R.gluedDiskMap_bijective

end PaperHalfPeriodRealization
end KsIndex.KarcherData
