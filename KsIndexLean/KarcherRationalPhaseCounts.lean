module

public import KsIndexLean.KarcherPhaseIndexValues
public import KsIndexLean.KarcherPhaseNullity
public import KsIndexLean.KarcherRationalSlitCorrespondence

@[expose] public section


/-! Phase-only index and bounded-field nullity over ℂ for rational phases
in `(0,1)` of the six-ended tower. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.FormIndex
variable [Fact (2 ≤ 3)] (R : PaperHalfPeriodRealization 3)

omit [Fact (2 ≤ 3)] in
lemma interior_rational_phase_indices (α : ℚ) (h0 : 0 < α) (h1 : α < 1) :
    0 < α.num.toNat ∧ α.num.toNat < α.den := by
  have he := nonnegative_rational_phase α (le_of_lt h0)
  have hd : (0 : ℝ) < α.den := by exact_mod_cast α.den_pos
  have h0r : (0 : ℝ) < (α : ℝ) := by exact_mod_cast h0
  have h1r : (α : ℝ) < 1 := by exact_mod_cast h1
  rw [← he] at h0r h1r
  constructor
  · exact_mod_cast (div_pos_iff_of_pos_right hd).mp h0r
  · exact_mod_cast (div_lt_one hd).mp h1r

/-- For each rational phase in `(0,1)`, the actual phase-only geometric index
is six in the open threshold band and four otherwise; bounded-field nullity
is two at either threshold and zero elsewhere. The quotient uses the reduced
denominator, and its deck character is `exp (2πiα)` by `rational_phase_character`. -/
theorem rational_phase_index_nullity (α : ℚ) (h0 : 0 < α) (h1 : α < 1) :
    letI : NeZero α.den := ⟨α.den_ne_zero⟩
    formIndex R.quotientJacobiQ
        (R.geometricSmoothPhase (m := α.den) α.num.toNat) =
      (if (α : ℝ) ∈ Set.Ioo KsIndex.Staircase.alphaStar
          (1 - KsIndex.Staircase.alphaStar) then 6 else 4) ∧
    Cardinal.toENat (Module.rank ℂ (R.geometricPhaseFiber (m := α.den) α.num.toNat)) =
      (if (α : ℝ) = KsIndex.Staircase.alphaStar ∨
          (α : ℝ) = 1 - KsIndex.Staircase.alphaStar then 2 else 0) := by
  let : NeZero α.den := ⟨α.den_ne_zero⟩
  obtain ⟨hn, hnm⟩ := interior_rational_phase_indices α h0 h1
  have hi := R.geometricSmoothPhase_index_eq_four_or_six (m := α.den) α.num.toNat hn hnm
  have hnul := R.geometricPhaseFiber_nullity_eq_endpoint (m := α.den) α.num.toNat hn hnm
  rw [nonnegative_rational_phase α (le_of_lt h0)] at hi hnul
  exact ⟨hi, hnul⟩

end KsIndex.KarcherData.PaperHalfPeriodRealization
