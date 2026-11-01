module

public import KsIndexLean.KarcherPhaseIndex
public import KsIndexLean.K3IndexComplete

@[expose] public section


/-! The phase-only index count for complex tests on the six-ended tower,
including the strict threshold convention. These formulas require `0 < n < m`. -/
noncomputable section
namespace KsIndex.KarcherData.PaperHalfPeriodRealization
open KsIndex.FormIndex KsIndex.Spectral
variable {m : ℕ} [Fact (2 ≤ 3)] [NeZero m] (R : PaperHalfPeriodRealization 3)

/-- The actual geometric index at an interior sampled translation phase. -/
theorem geometricSmoothPhase_index_eq_phaseCount (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    formIndex R.quotientJacobiQ (R.geometricSmoothPhase (m := m) n) =
      ((2 + 2 * KsIndex.Staircase.phaseCount ((n : ℝ) / m) : ℕ) : ℕ∞) := by
  rw [R.geometricSmoothPhase_index_eq_sum_rotation, Fin.sum_univ_three]
  change (formIndex R.quotientJacobiQ (R.geometricSmoothJointSector n 0) +
    formIndex R.quotientJacobiQ (R.geometricSmoothJointSector n 1) +
    formIndex R.quotientJacobiQ (R.geometricSmoothJointSector n 2)) = _
  rw [R.geometricSmoothJointSector_index_eq_model,
    R.geometricSmoothJointSector_index_eq_model,
    R.geometricSmoothJointSector_index_eq_model,
    paperSmooth_nonzeroPhase_trivial_index m n hn hnm,
    paperSmoothSector_index_eq_slit, paperSmoothSector_index_eq_slit,
    paperSlit_sampled_index_eq_phaseCount m n hn hnm 1 (Or.inl rfl),
    paperSlit_sampled_index_eq_phaseCount m n hn hnm 2 (Or.inr rfl)]
  push_cast
  rw [two_mul]
  ac_rfl

/-- The index is six strictly between the thresholds and four elsewhere in
an interior translation phase, including either threshold itself. -/
theorem geometricSmoothPhase_index_eq_four_or_six (n : ℕ) (hn : 0 < n) (hnm : n < m) :
    formIndex R.quotientJacobiQ (R.geometricSmoothPhase (m := m) n) =
      if (n : ℝ) / m ∈ Set.Ioo KsIndex.Staircase.alphaStar
          (1 - KsIndex.Staircase.alphaStar) then 6 else 4 := by
  rw [R.geometricSmoothPhase_index_eq_phaseCount n hn hnm]
  unfold KsIndex.Staircase.phaseCount
  split_ifs <;> norm_num

end KsIndex.KarcherData.PaperHalfPeriodRealization
