module

public import KsIndexLean.AlphaStarNumericalPeriods
public import KsIndexLean.KarcherGeometricCapstone

@[expose] public section


/-! Explicit geometric indices and bounded-field nullity through period 2298.
These results use both optional numerical certificate stacks. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization

/-- The numerical interval determines both invariants for every positive period at most 2298. -/
theorem geometric_numerical_periods [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)
    (m : ℕ) [NeZero m] (hm : m ≤ 2298) :
    R.geometricIndex (m := m) =
      ((6 * m - 4 * (4323617 * m / 10000000) - 3 : ℕ) : ℕ∞) ∧
    R.geometricNullity (m := m) = 3 := by
  have hpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  constructor
  · rw [R.geometricIndex_three m, Staircase.alphaStar_floor_le_2298 hpos hm]
  · rw [R.geometricNullity_three m]
    exact if_neg (Staircase.alphaStar_nonresonant_le_2298 hpos hm)

/-- One EW realization satisfies all the certified period evaluations. -/
theorem exists_geometric_numerical_periods :
    letI : Fact (2 ≤ 3) := ⟨by omega⟩
    ∃ R : PaperHalfPeriodRealization 3, ∀ (m : ℕ) [NeZero m], m ≤ 2298 →
      R.geometricIndex (m := m) =
        ((6 * m - 4 * (4323617 * m / 10000000) - 3 : ℕ) : ℕ∞) ∧
      R.geometricNullity (m := m) = 3 := by
  let : Fact (2 ≤ 3) := ⟨by omega⟩
  obtain ⟨R⟩ := exists_paperHalfPeriodRealization (k := 3)
  exact ⟨R, fun m _ hm => R.geometric_numerical_periods m hm⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
