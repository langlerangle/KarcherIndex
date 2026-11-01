module

public import KsIndexLean.KarcherGeometricInvariants
public import KsIndexLean.D5Discharge
public import KsIndexLean.GeneralCapstone
public import KsIndexLean.K3IndexComplete
public import KsIndexLean.PaperChainNullityExact

@[expose] public section


/-! Index and bounded-field nullity formulas for the actual EW quotients.
The invariants here use complex test spaces and complex Jacobi fields. -/
noncomputable section
open scoped Classical
namespace KsIndex.KarcherData.PaperHalfPeriodRealization

/-- Index of the two-period quotient, with complex test functions. -/
theorem geometricIndex_two {k : ℕ} [Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) (hk : 3 ≤ k) :
    R.geometricIndex (m := 2) = ((4 * k - 3 : ℕ) : ℕ∞) := by
  rw [R.geometricIndex_eq_model]
  exact Trace.indSurface_two_val_final hk

/-- Complex dimension of bounded Jacobi fields on the two-period quotient. -/
theorem geometricNullity_two {k : ℕ} [Fact (2 ≤ k)]
    (R : PaperHalfPeriodRealization k) (hk : 3 ≤ k) :
    R.geometricNullity (m := 2) = 3 := by
  rw [R.geometricNullity_eq_model]
  exact NullityDecomp.nulSurface_eq_three hk

/-- Index formula for the six-ended family, including threshold equality. -/
theorem geometricIndex_three [Fact (2 ≤ 3)]
    (R : PaperHalfPeriodRealization 3) (m : ℕ) [NeZero m] :
    R.geometricIndex (m := m) =
      ((6 * m - 4 * ⌊(m : ℝ) * Staircase.alphaStar⌋₊ - 3 : ℕ) : ℕ∞) := by
  rw [R.geometricIndex_eq_model]
  exact Spectral.indSurface_three_eq_floor m

/-- The resonant nullity dichotomy on the actual quotient, over ℂ. -/
theorem geometricNullity_three [Fact (2 ≤ 3)]
    (R : PaperHalfPeriodRealization 3) (m : ℕ) [NeZero m] :
    R.geometricNullity (m := m) =
      if ∃ z : ℤ, (m : ℝ) * Staircase.alphaStar = (z : ℝ) then 7 else 3 := by
  rw [R.geometricNullity_eq_model]
  exact PaperSlitTransport.nulSurface_eq_seven_or_three

/-- The double-period formulas hold for a realization constructed from the EW data. -/
theorem exists_geometric_double_period {k : ℕ} (hk : 3 ≤ k) :
    letI : Fact (2 ≤ k) := ⟨by omega⟩
    ∃ R : PaperHalfPeriodRealization k,
      R.geometricIndex (m := 2) = ((4 * k - 3 : ℕ) : ℕ∞) ∧
      R.geometricNullity (m := 2) = 3 := by
  let : Fact (2 ≤ k) := ⟨by omega⟩
  obtain ⟨R⟩ := exists_paperHalfPeriodRealization (k := k)
  exact ⟨R, R.geometricIndex_two hk, R.geometricNullity_two hk⟩

/-- One EW realization and one threshold give both formulas for every period. -/
theorem exists_geometric_six_end_formulas :
    letI : Fact (2 ≤ 3) := ⟨by omega⟩
    ∃ R : PaperHalfPeriodRealization 3, ∃ a : ℝ,
      a ∈ Set.Ioo (1 / 3 : ℝ) (1 / 2) ∧
      ∀ (m : ℕ) [NeZero m],
        R.geometricIndex (m := m) =
          ((6 * m - 4 * ⌊(m : ℝ) * a⌋₊ - 3 : ℕ) : ℕ∞) ∧
        R.geometricNullity (m := m) =
          if ∃ z : ℤ, (m : ℝ) * a = (z : ℝ) then 7 else 3 := by
  let : Fact (2 ≤ 3) := ⟨by omega⟩
  obtain ⟨R⟩ := exists_paperHalfPeriodRealization (k := 3)
  exact ⟨R, Staircase.alphaStar, Staircase.alphaStar_mem_Ioo,
    fun m _ => ⟨R.geometricIndex_three m, R.geometricNullity_three m⟩⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
