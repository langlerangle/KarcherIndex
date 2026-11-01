module

public import KsIndexLean.KarcherPeriodDiskCopies

@[expose] public section


/-! The actual quotient is covered by the model's ordered ZMod (2m) disk copies. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
local instance : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩

def evenCopyIndex (j : ZMod m) : ZMod (2 * m) := (2 * j.val : ℕ)
def oddCopyIndex (j : ZMod m) : ZMod (2 * m) := (2 * j.val + 1 : ℕ)

lemma evenCopyIndex_val (j : ZMod m) : (evenCopyIndex j).val = 2 * j.val := by
  apply ZMod.val_natCast_of_lt
  have := ZMod.val_lt j
  omega

lemma oddCopyIndex_val (j : ZMod m) : (oddCopyIndex j).val = 2 * j.val + 1 := by
  apply ZMod.val_natCast_of_lt
  have := ZMod.val_lt j
  omega

/-- The original copy order: the even half-period followed by its upper reflection. -/
def orderedDiskPoint (R : PaperHalfPeriodRealization k) (n : ZMod (2 * m))
    (w : PuncturedClosedDisk k) :
    HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m :=
  if n.val % 2 = 0 then R.evenPeriodPoint m ((n.val / 2 : ℕ) : ℤ) w
  else R.oddPeriodPoint m ((n.val / 2 : ℕ) : ℤ) w

lemma orderedDiskPoint_even (R : PaperHalfPeriodRealization k) (j : ZMod m)
    (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint (evenCopyIndex j) w = R.evenPeriodPoint m (j.val : ℤ) w := by
  simp only [orderedDiskPoint, evenCopyIndex_val]
  have hm : (2 * j.val) % 2 = 0 := by omega
  have hd : (2 * j.val) / 2 = j.val := by omega
  rw [ite_eq_left hm, hd]

lemma orderedDiskPoint_odd (R : PaperHalfPeriodRealization k) (j : ZMod m)
    (w : PuncturedClosedDisk k) :
    R.orderedDiskPoint (oddCopyIndex j) w = R.oddPeriodPoint m (j.val : ℤ) w := by
  simp only [orderedDiskPoint, oddCopyIndex_val]
  have hm : (2 * j.val + 1) % 2 ≠ 0 := by omega
  have hd : (2 * j.val + 1) / 2 = j.val := by omega
  rw [ite_eq_right hm, hd]

lemma copyIndex_cases (n : ZMod (2 * m)) :
    ∃ j : ZMod m, n = evenCopyIndex j ∨ n = oddCopyIndex j := by
  have hn := ZMod.val_lt n
  have hd : n.val / 2 < m := by omega
  let j : ZMod m := (n.val / 2 : ℕ)
  have hj : j.val = n.val / 2 := ZMod.val_natCast_of_lt hd
  refine ⟨j, ?_⟩
  by_cases he : n.val % 2 = 0
  · left
    apply ZMod.val_injective
    rw [evenCopyIndex_val, hj]
    omega
  · right
    apply ZMod.val_injective
    rw [oddCopyIndex_val, hj]
    omega

/-- Every actual quotient point is represented by one of the prescribed 2m disks. -/
theorem orderedDiskPoint_surjective (R : PaperHalfPeriodRealization k) :
    Function.Surjective (fun p : ZMod (2 * m) × PuncturedClosedDisk k =>
      R.orderedDiskPoint p.1 p.2) := by
  intro q
  obtain ⟨j, w, he | he⟩ := R.periodDiskCopies_cover m q
  · refine ⟨(evenCopyIndex (j : ZMod m), w), ?_⟩
    change R.orderedDiskPoint (evenCopyIndex (j : ZMod m)) w = q
    rw [orderedDiskPoint_even, he]
    exact (R.evenPeriodPoint_eq_iff m _ _ w w).mpr ⟨by simp, rfl⟩
  · refine ⟨(oddCopyIndex (j : ZMod m), w), ?_⟩
    change R.orderedDiskPoint (oddCopyIndex (j : ZMod m)) w = q
    rw [orderedDiskPoint_odd, he]
    exact (R.oddPeriodPoint_eq_iff m _ _ w w).mpr ⟨by simp, rfl⟩

lemma orderedDiskPoint_injective (R : PaperHalfPeriodRealization k) (n : ZMod (2 * m)) :
    Function.Injective (R.orderedDiskPoint n) := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · intro w v he
    simp only [orderedDiskPoint_even] at he
    exact ((R.evenPeriodPoint_eq_iff m _ _ w v).mp he).2
  · intro w v he
    simp only [orderedDiskPoint_odd] at he
    exact ((R.oddPeriodPoint_eq_iff m _ _ w v).mp he).2

end KsIndex.KarcherData.PaperHalfPeriodRealization
