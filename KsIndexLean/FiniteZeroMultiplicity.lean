module

public import KsIndexLean.FiniteSolutionSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral.PositiveCompactSolution
open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H] (S : KsIndex.Spectral.PositiveCompactSolution H)

/-- Counts in a finite sector include the empty sector and an entirely
nonpositive spectrum. No infinite-dimensional enumeration is assumed. -/
def finiteStrictCount (c L : ℝ) : ℕ :=
  (Finset.univ.filter fun i => S.finiteReciprocalShift c i < L).card

def finiteWeakCount (c L : ℝ) : ℕ :=
  (Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ L).card

lemma finiteReciprocalShift_eq_zero_iff (c : ℝ) (i : Fin (Module.finrank ℂ H)) :
    S.finiteReciprocalShift c i = 0 ↔ S.finiteEigenvalues i = c⁻¹ := by
  change (S.finiteEigenvalues i)⁻¹ - c = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    simpa only [inv_inv] using congrArg (fun r : ℝ => r⁻¹) h
  · intro h
    rw [h, inv_inv]

lemma finite_zero_multiplicity (c : ℝ) :
    Module.finrank ℂ (eigenspace S.operator.toLinearMap ((c⁻¹ : ℝ) : ℂ)) =
      S.finiteWeakCount c 0 - S.finiteStrictCount c 0 := by
  classical
  rw [← S.finiteEigenvalues_multiplicity]
  have he : (Finset.univ.filter fun i => (S.finiteEigenvalues i : ℂ) =
      ((c⁻¹ : ℝ) : ℂ)) =
      (Finset.univ.filter fun i => S.finiteReciprocalShift c i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Complex.ofReal_inj]
    exact (S.finiteReciprocalShift_eq_zero_iff c i).symm
  rw [he]
  have hp := (Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ 0).card_filter_add_card_filter_not (fun i => S.finiteReciprocalShift c i < 0)
  have hn : ((Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ 0).filter
      fun i => S.finiteReciprocalShift c i < 0) =
      (Finset.univ.filter fun i => S.finiteReciprocalShift c i < 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_iff_right_of_imp le_of_lt
  have hz : ((Finset.univ.filter fun i => S.finiteReciprocalShift c i ≤ 0).filter
      fun i => ¬ S.finiteReciprocalShift c i < 0) =
      (Finset.univ.filter fun i => S.finiteReciprocalShift c i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact le_antisymm_iff.symm
  rw [hn, hz] at hp
  unfold finiteWeakCount finiteStrictCount
  omega

end KsIndex.Spectral.PositiveCompactSolution
