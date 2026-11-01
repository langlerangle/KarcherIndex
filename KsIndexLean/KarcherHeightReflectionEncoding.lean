module

public import KsIndexLean.KarcherHeightReflection

@[expose] public section


/-! The horizontal reflection reverses ordered copy indices by n ↦ -n-1. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

lemma reflected_evenCopyIndex {m : ℕ} [NeZero m] (j : ZMod m) :
    -evenCopyIndex j - 1 = oddCopyIndex (-j-1) := by
  have hj := ZMod.val_lt j
  have hn : m-1-j.val < m := by omega
  have hs : (m-1-j.val)+j.val+1 = m := by omega
  have hc := congrArg (fun n : ℕ => (n : ZMod m)) hs
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, ZMod.natCast_zmod_val] at hc
  have he : (-j-1 : ZMod m) = ((m-1-j.val : ℕ) : ZMod m) := by
    linear_combination -hc
  have hv : (-j-1 : ZMod m).val = m-1-j.val := by
    rw [he]
    exact ZMod.val_natCast_of_lt hn
  have hs2 : (2*j.val+1)+(2*(m-1-j.val)+1) = 2*m := by omega
  have hc2 := congrArg (fun n : ℕ => (n : ZMod (2*m))) hs2
  rw [ZMod.natCast_self] at hc2
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hc2
  simp only [evenCopyIndex, oddCopyIndex, hv, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  linear_combination -hc2

lemma reflected_oddCopyIndex {m : ℕ} [NeZero m] (j : ZMod m) :
    -oddCopyIndex j - 1 = evenCopyIndex (-j-1) := by
  have he := reflected_evenCopyIndex j
  simp only [← evenCopyIndex_succ] at he ⊢
  linear_combination he


lemma periodHeightReflection_orderedDiskPoint (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m] (n : ZMod (2*m)) (w : PuncturedClosedDisk k) :
    R.periodHeightReflection m (R.orderedDiskPoint n w) = R.orderedDiskPoint (-n-1) w := by
  obtain ⟨j, rfl | rfl⟩ := copyIndex_cases n
  · rw [reflected_evenCopyIndex, orderedDiskPoint_even]
    have hj : (((-(j.val : ℤ)-1) : ℤ) : ZMod m) = -j-1 := by simp
    rw [← hj, orderedDiskPoint_odd_int]
    exact R.periodHeightReflection_evenPoint m _ w
  · rw [reflected_oddCopyIndex, orderedDiskPoint_odd]
    have hj : (((-(j.val : ℤ)-1) : ℤ) : ZMod m) = -j-1 := by simp
    rw [← hj, orderedDiskPoint_even_int]
    exact R.periodHeightReflection_oddPoint m _ w

lemma encode_heightReflection_pullback (R : PaperHalfPeriodRealization k)
    {m : ℕ} [NeZero m]
    (f : HeightLift.PeriodQuotient (extendedEWMap h.out (reflectionBasepoint k) R.C) m → ℂ) :
    encodeDiskFunction (R.diskFunctionPullback (f ∘ R.periodHeightReflection m)) =
      fun n z => encodeDiskFunction (R.diskFunctionPullback f) (-n-1) z := by
  funext n z
  by_cases hz : z ∉ Surface.punctures k ∧ ‖z‖ ≤ 1
  · let w : PuncturedClosedDisk k := ⟨⟨z,hz.1⟩,hz.2⟩
    change encodeDiskFunction _ n w.val.val = encodeDiskFunction _ (-n-1) w.val.val
    rw [encodeDiskFunction_on_disk, encodeDiskFunction_on_disk]
    change f (R.periodHeightReflection m (R.orderedDiskPoint n w)) =
      f (R.orderedDiskPoint (-n-1) w)
    rw [R.periodHeightReflection_orderedDiskPoint]
  · simp only [encodeDiskFunction, dite_eq_right hz]

end KsIndex.KarcherData.PaperHalfPeriodRealization
