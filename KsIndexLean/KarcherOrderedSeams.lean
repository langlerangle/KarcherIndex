module

public import KsIndexLean.KarcherFiniteDiskCopies

@[expose] public section


/-! The actual copy maps respect the precise cyclic seam convention of Surface. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] [NeZero m]
local instance : NeZero (2 * m) := ⟨by have := NeZero.ne m; omega⟩

omit [NeZero m] in
lemma evenCopyIndex_succ (j : ZMod m) : evenCopyIndex j + 1 = oddCopyIndex j := by
  simp only [evenCopyIndex, oddCopyIndex, Nat.cast_add, Nat.cast_one]

lemma oddCopyIndex_succ (j : ZMod m) : oddCopyIndex j + 1 = evenCopyIndex (j + 1) := by
  have hv : (j + 1).val = (j.val + 1) % m := by
    conv_lhs => rw [← ZMod.natCast_zmod_val j, ← Nat.cast_one, ← Nat.cast_add]
    exact ZMod.val_natCast _ _
  have hj := ZMod.val_lt j
  by_cases hl : j.val + 1 < m
  · rw [evenCopyIndex, hv, Nat.mod_eq_of_lt hl, oddCopyIndex]
    push_cast
    ring
  · have he : j.val + 1 = m := by omega
    rw [evenCopyIndex, hv, he, Nat.mod_self, mul_zero, Nat.cast_zero]
    have hn : 2 * j.val + 1 + 1 = 2 * m := by omega
    change ((2 * j.val + 1 : ℕ) : ZMod (2 * m)) + 1 = 0
    calc
      _ = ((2 * j.val + 1 + 1 : ℕ) : ZMod (2 * m)) := by push_cast; rfl
      _ = 0 := by rw [hn]; simp

omit h in
lemma seamArc_evenCopyIndex (j : ZMod m) :
    Surface.seamArc k m (evenCopyIndex j) = Surface.arc k 1 := by
  have he : Surface.parity m (evenCopyIndex j + 1) = 1 := by
    simp only [evenCopyIndex, map_add, map_one, Nat.cast_mul, map_mul]
    norm_num
    rw [map_ofNat]
    have htwo : (2 : ZMod 2) = 0 := by decide
    exact Or.inl htwo
  simp only [Surface.seamArc, he]
  rfl

omit h in
lemma seamArc_oddCopyIndex (j : ZMod m) :
    Surface.seamArc k m (oddCopyIndex j) = Surface.arc k 0 := by
  have he : Surface.parity m (oddCopyIndex j + 1) = 0 := by
    simp only [oddCopyIndex, map_add, map_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one, map_mul]
    norm_num
    rw [map_ofNat]
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo]
    simp only [zero_mul, zero_add]
    change (1 : ZMod 2) + 1 = 0
    decide
  simp only [Surface.seamArc, he]
  rfl

/-- Each model seam is an actual equality of quotient points. This is an
implication, since for m=1 the same pair of disks also shares the other seam. -/
theorem orderedDiskPoint_glues (R : PaperHalfPeriodRealization k)
    (n : ZMod (2 * m)) (w : PuncturedClosedDisk k)
    (hw : w.val.val ∈ Surface.seamArc k m n) :
    R.orderedDiskPoint n w = R.orderedDiskPoint (n + 1) w := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · rw [seamArc_evenCopyIndex] at hw
    rw [evenCopyIndex_succ, orderedDiskPoint_even, orderedDiskPoint_odd]
    exact (R.evenPeriodPoint_eq_odd_iff m _ _ w w).mpr ⟨rfl, Or.inl ⟨rfl, hw⟩⟩
  · rw [seamArc_oddCopyIndex] at hw
    rw [oddCopyIndex_succ, orderedDiskPoint_odd, orderedDiskPoint_even]
    symm
    exact (R.evenPeriodPoint_eq_odd_iff m _ _ w w).mpr
      ⟨rfl, Or.inr ⟨by simp, hw⟩⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
