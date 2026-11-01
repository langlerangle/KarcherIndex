module

public import KsIndexLean.AlphaStarFourModeBound
public import KsIndexLean.KarcherGeometricCapstone

@[expose] public section


/-! Certified phase bounds and the five-period six-ended index and nullity
for a supplied paper half-period realization. -/
noncomputable section
namespace KsIndex.AlphaFourMode

lemma five_alphaStar_bounds : (2:ℝ) < 5*Staircase.alphaStar ∧ 5*Staircase.alphaStar < 3 := by
  have hl := two_fifths_lt_alphaStar
  have hu := Staircase.alphaStar_mem_Ioo.2
  constructor <;> linarith

lemma five_alphaStar_floor : ⌊(5:ℝ)*Staircase.alphaStar⌋₊ = 2 := by
  rw [Nat.floor_eq_iff (show (0:ℝ) ≤ 5*Staircase.alphaStar by
    have h := five_alphaStar_bounds.1; linarith)]
  constructor <;> have h := five_alphaStar_bounds <;> norm_num <;> linarith

lemma five_alphaStar_nonresonant : ¬ ∃ z : ℤ, (5:ℝ)*Staircase.alphaStar = (z:ℝ) := by
  rintro ⟨z, hz⟩
  have h := five_alphaStar_bounds
  rw [hz] at h
  have h1 : (2:ℤ) < z := by exact_mod_cast h.1
  have h2 : z < (3:ℤ) := by exact_mod_cast h.2
  omega

end KsIndex.AlphaFourMode
namespace KsIndex.KarcherData.PaperHalfPeriodRealization

/-- Supplemental evaluation of the six-ended, five-period index and nullity. -/
theorem geometric_five_period [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3) :
    R.geometricIndex (m := 5) = 19 ∧ R.geometricNullity (m := 5) = 3 := by
  constructor
  · rw [R.geometricIndex_three 5]
    norm_num [AlphaFourMode.five_alphaStar_floor]
  · rw [R.geometricNullity_three 5]
    simp only [Nat.cast_ofNat, ite_eq_right AlphaFourMode.five_alphaStar_nonresonant]

end KsIndex.KarcherData.PaperHalfPeriodRealization
