module

public import KsIndexLean.SpectralEigenspaceCoordinates
public import KsIndexLean.OrderedSpectralCounts
public import KsIndexLean.FiniteZeroMultiplicity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral.PositiveCompactSolution
open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : KsIndex.Spectral.PositiveCompactSolution H)

section Infinite
variable [Infinite S.eigenbasisIndex]

lemma infiniteReciprocalShift_eq_level_iff (c L : ℝ) (i : ℕ) :
    S.infiniteReciprocalShift c i = L ↔ S.infiniteEigenvalues i = (L + c)⁻¹ := by
  change (S.infiniteEigenvalues i)⁻¹ - c = L ↔ _
  rw [sub_eq_iff_eq_add]
  constructor
  · intro h
    have he := congrArg (fun r : ℝ => r⁻¹) h
    simpa only [inv_inv] using he
  · intro h
    rw [h, inv_inv]

/-- Every level block of the reciprocal-shift spectrum has exactly its complex
eigenspace dimension. Both counts include repeated basis eigenvalues. -/
lemma infinite_level_multiplicity (c L : ℝ) :
    Module.finrank ℂ (eigenspace S.operator.toLinearMap (((L + c)⁻¹ : ℝ) : ℂ)) =
      weakSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) L -
      strictSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) L := by
  let a := strictSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) L
  let z := weakSpectralCount (S.infiniteReciprocalShift c) (S.infiniteReciprocalShift_tendsto_atTop c) L
  have hs (i : ℕ) : i ∈ Finset.Ico a z ↔ S.infiniteEigenvalues i = (L + c)⁻¹ := by
    rw [Finset.mem_Ico]
    have he := eq_level_iff_count_interval (S.infiniteReciprocalShift c)
      (S.infiniteReciprocalShift_tendsto_atTop c) (S.infiniteReciprocalShift_monotone c) L i
    exact he.symm.trans (S.infiniteReciprocalShift_eq_level_iff c L i)
  have h := eigenspace_finrank_eq_block_card S.operator S.symmetric S.infiniteEigenbasis
    S.infiniteEigenvalues S.infiniteEigenbasis_equation ((L + c)⁻¹) (Finset.Ico a z) hs
  simpa only [Nat.card_Ico] using h

end Infinite

section Finite
variable [FiniteDimensional ℂ H]

lemma finiteReciprocalShift_eq_level_iff (c L : ℝ) (i : Fin (Module.finrank ℂ H)) :
    S.finiteReciprocalShift c i = L ↔ S.finiteEigenvalues i = (L + c)⁻¹ := by
  change (S.finiteEigenvalues i)⁻¹ - c = L ↔ _
  rw [sub_eq_iff_eq_add]
  constructor
  · intro h
    simpa only [inv_inv] using congrArg (fun r : ℝ => r⁻¹) h
  · intro h
    rw [h, inv_inv]

lemma finite_level_multiplicity (c L : ℝ) :
    Module.finrank ℂ (eigenspace S.operator.toLinearMap (((L + c)⁻¹ : ℝ) : ℂ)) =
      S.finiteWeakCount c L - S.finiteStrictCount c L := by
  classical
  rw [← S.finiteEigenvalues_multiplicity]
  have he : (Finset.univ.filter fun i => (S.finiteEigenvalues i : ℂ) =
      (((L + c)⁻¹ : ℝ) : ℂ)) =
      (Finset.univ.filter fun i => S.finiteReciprocalShift c i = L) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Complex.ofReal_inj]
    exact (S.finiteReciprocalShift_eq_level_iff c L i).symm
  rw [he]
  have hp := (Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ L).card_filter_add_card_filter_not (fun i => S.finiteReciprocalShift c i < L)
  have hn : ((Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ L).filter
      fun i => S.finiteReciprocalShift c i < L) =
      (Finset.univ.filter fun i => S.finiteReciprocalShift c i < L) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right_of_imp le_of_lt
  have hz : ((Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ L).filter
      fun i => ¬ S.finiteReciprocalShift c i < L) =
      (Finset.univ.filter fun i => S.finiteReciprocalShift c i = L) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_antisymm_iff.symm
  rw [hn, hz] at hp
  unfold finiteWeakCount finiteStrictCount
  omega

end Finite
end KsIndex.Spectral.PositiveCompactSolution
