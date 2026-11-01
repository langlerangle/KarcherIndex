module

public import KsIndexLean.KarcherGeometricCapstone

@[expose] public section


/-! The introductory five-period-list corollary, using the original threshold bounds.
The genus reformulations are deliberately not asserted. -/
noncomputable section
namespace KsIndex.Staircase

/-- The floor values for the five periods in the paper's introductory corollary. -/
def smallPeriodFloor (m : ℕ) : ℕ := if m = 1 ∨ m = 2 then 0 else if m = 6 then 2 else 1

lemma smallPeriod_interval {m : ℕ} (hm : m ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    (smallPeriodFloor m : ℝ) < (m : ℝ) * alphaStar ∧
      (m : ℝ) * alphaStar < (smallPeriodFloor m : ℝ) + 1 := by
  have hl := alphaStar_gt_third
  have hu := alphaStar_lt_half
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [smallPeriodFloor] <;> constructor <;> linarith

lemma smallPeriod_floor {m : ℕ} (hm : m ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ⌊(m : ℝ) * alphaStar⌋₊ = smallPeriodFloor m := by
  rw [Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) alphaStar_pos.le)]
  exact ⟨(smallPeriod_interval hm).1.le, (smallPeriod_interval hm).2⟩

lemma smallPeriod_nonresonant {m : ℕ} (hm : m ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    ¬ ∃ z : ℤ, (m : ℝ) * alphaStar = (z : ℝ) := by
  rintro ⟨z, hz⟩
  obtain ⟨hl, hu⟩ := smallPeriod_interval hm
  rw [hz] at hl hu
  have hli : (smallPeriodFloor m : ℤ) < z := by exact_mod_cast hl
  have hui : z < (smallPeriodFloor m : ℤ) + 1 := by exact_mod_cast hu
  omega

end KsIndex.Staircase
namespace KsIndex.KarcherData.PaperHalfPeriodRealization

/-- Corollary 580: index and bounded Jacobi nullity for the five named periods. -/
theorem geometric_small_periods [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)
    (m : ℕ) [NeZero m] (hm : m ∈ ({1, 2, 3, 4, 6} : Finset ℕ)) :
    R.geometricIndex (m := m) =
      ((if m = 1 ∨ m = 3 then 4 * m - 1 else 4 * m + 1 : ℕ) : ℕ∞) ∧
    R.geometricNullity (m := m) = 3 := by
  constructor
  · rw [R.geometricIndex_three m, Staircase.smallPeriod_floor hm]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [Staircase.smallPeriodFloor]
  · rw [R.geometricNullity_three m]
    exact ite_eq_right (Staircase.smallPeriod_nonresonant hm)

/-- A realization constructed from the EW data satisfies all five evaluations. -/
theorem exists_geometric_small_periods :
    letI : Fact (2 ≤ 3) := ⟨by omega⟩
    ∃ R : PaperHalfPeriodRealization 3, ∀ (m : ℕ) [NeZero m],
      m ∈ ({1, 2, 3, 4, 6} : Finset ℕ) →
      R.geometricIndex (m := m) =
        ((if m = 1 ∨ m = 3 then 4 * m - 1 else 4 * m + 1 : ℕ) : ℕ∞) ∧
      R.geometricNullity (m := m) = 3 := by
  let : Fact (2 ≤ 3) := ⟨by omega⟩
  obtain ⟨R⟩ := exists_paperHalfPeriodRealization (k := 3)
  exact ⟨R, fun m _ hm => R.geometric_small_periods m hm⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
