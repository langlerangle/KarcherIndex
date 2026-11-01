module

public import KsIndexLean.AlphaOuterTailAssembly
public import KsIndexLean.AlphaCompensatedGroupEnergy

@[expose] public section


/-! # Weighted summability of compensated-group tails

The energy theorem `compensatedPowerArcGroup_energy` supplies summability of the
`(6m+1)`-weighted squares from index 1024. Reindexing and removing a finite prefix
give summability for any natural-number cutoff, for the two specified exponents
and endpoints 14 or 15. -/
noncomputable section
namespace KsIndex.AlphaRemarkTrial
open CircleQ AlphaResidual PowerArc OppositeHalf

/-- The `(6m+1)`-weighted squared group tail is summable (any cutoff `T`). -/
theorem group_weighted_tail_summable (β r κ w : ℝ)
    (hβ : β = 4323618 / 10000000 ∨ β = 5676382 / 10000000) (hr : r = 14 ∨ r = 15) (T : ℕ) :
    Summable (fun m : ℕ =>
      if T < m then (6 * (m : ℝ) + 1) * compensatedPowerArcGroup β r κ w m ^ 2 else 0) := by
  have he := (compensatedPowerArcGroup_energy β r κ w 1024 hβ hr (le_refl 1024)).1
  rw [← summable_nat_add_iff 1024]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) he
  · simp only [Nat.add_comm n 1024]; split_ifs <;> positivity
  · simp only [Nat.add_comm n 1024]; split_ifs with h
    · exact le_refl _
    · positivity

end KsIndex.AlphaRemarkTrial

#print axioms KsIndex.AlphaRemarkTrial.group_weighted_tail_summable
