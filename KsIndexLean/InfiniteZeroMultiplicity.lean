module

public import KsIndexLean.SpectralEigenspaceCoordinates
public import KsIndexLean.OrderedSpectralCounts

@[expose] public section


noncomputable section
namespace KsIndex.Spectral.PositiveCompactSolution
open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : KsIndex.Spectral.PositiveCompactSolution H) [Infinite S.eigenbasisIndex]

lemma infiniteReciprocalShift_eq_zero_iff (c : ℝ) (i : ℕ) :
    S.infiniteReciprocalShift c i = 0 ↔ S.infiniteEigenvalues i = c⁻¹ := by
  change (S.infiniteEigenvalues i)⁻¹ - c = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    have he := congrArg (fun r : ℝ => r⁻¹) h
    simpa only [inv_inv] using he
  · intro h
    rw [h, inv_inv]

/-- The zero block of the reciprocal-shift spectrum has exactly its complex
eigenspace dimension. Both counts include repeated basis eigenvalues. -/
lemma infinite_zero_multiplicity (c : ℝ) :
    Module.finrank ℂ (eigenspace S.operator.toLinearMap ((c⁻¹ : ℝ) : ℂ)) =
      weakSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) 0 -
      strictSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) 0 := by
  let a := strictSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) 0
  let z := weakSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) 0
  have hs (i : ℕ) : i ∈ Finset.Ico a z ↔ S.infiniteEigenvalues i = c⁻¹ := by
    rw [Finset.mem_Ico]
    have he := eq_level_iff_count_interval (S.infiniteReciprocalShift c)
      (S.infiniteReciprocalShift_tendsto_atTop c) (S.infiniteReciprocalShift_monotone c) 0 i
    exact he.symm.trans (S.infiniteReciprocalShift_eq_zero_iff c i)
  have h := eigenspace_finrank_eq_block_card S.operator S.symmetric S.infiniteEigenbasis
    S.infiniteEigenvalues S.infiniteEigenbasis_equation (c⁻¹) (Finset.Ico a z) hs
  simpa only [Nat.card_Ico] using h

end KsIndex.Spectral.PositiveCompactSolution
