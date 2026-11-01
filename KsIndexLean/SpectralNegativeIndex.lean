module

public import KsIndexLean.MinMaxNonpositiveCount
public import KsIndexLean.NegativeDensity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Filter

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma negative_trial_dimension_le_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (b : ℕ → H) (ν : ℕ → ℝ)
    (hν : Tendsto ν atTop atTop)
    (htail : ∀ n u, (∀ i < n, inner ℂ (b i) (J u) = 0) → ν n * ‖J u‖ ^ 2 ≤ Q u)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (hW : ∀ u : W, u ≠ 0 → Q u < 0) :
    Module.finrank ℂ W ≤ strictSpectralCount ν hν 0 := by
  by_contra hd
  obtain ⟨u, hu, horth⟩ := exists_nonzero_orthogonal_before J b W
    (strictSpectralCount ν hν 0) (by omega)
  have hlo := htail _ u horth
  have hnonneg := mul_nonneg (strictSpectralCount_spec ν hν 0) (sq_nonneg ‖J u‖)
  have hneg := hW u hu
  linarith

lemma exists_negative_trial_of_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (hJ : Function.Injective J) (ν : ℕ → ℝ)
    (hν : Tendsto ν atTop atTop) (hmono : Monotone ν)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = strictSpectralCount ν hν 0 ∧ ∀ u : W, u ≠ 0 → Q u < 0 := by
  by_cases hc : strictSpectralCount ν hν 0 = 0
  · refine ⟨⊥, inferInstance, by simp [hc], ?_⟩
    intro u hu
    exact False.elim (hu (Subsingleton.elim _ _))
  · let n := strictSpectralCount ν hν 0 - 1
    have hn : n < strictSpectralCount ν hν 0 := by dsimp [n]; omega
    have hv := (lt_level_iff_lt_strictSpectralCount ν hν hmono 0 n).mpr hn
    obtain ⟨W, hW, hd, hb⟩ := (hmm n (ν n)).mp le_rfl
    refine ⟨W, hW, by dsimp [n] at hd; omega, ?_⟩
    intro u hu
    have hbulk : J u ≠ 0 := by
      intro he
      exact hu (Subtype.ext (hJ (he.trans J.map_zero.symm)))
    exact (hb u).trans_lt (mul_neg_of_neg_of_pos hv (sq_pos_of_pos (norm_pos_iff.mpr hbulk)))

/-- The variational negative index equals the strict spectral count at zero. -/
lemma negativeIndex_eq_strictSpectralCount
    (Q : E → ℝ) (J : E →L[ℂ] H) (hJ : Function.Injective J) (b : ℕ → H) (ν : ℕ → ℝ)
    (hν : Tendsto ν atTop atTop) (hmono : Monotone ν)
    (htail : ∀ n u, (∀ i < n, inner ℂ (b i) (J u) = 0) → ν n * ‖J u‖ ^ 2 ≤ Q u)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2) :
    KsIndex.NegativeDensity.negativeIndex Q = (strictSpectralCount ν hν 0 : ℕ∞) := by
  apply le_antisymm
  · unfold KsIndex.NegativeDensity.negativeIndex
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfd => ?_
    let := hfd
    have hd := negative_trial_dimension_le_count Q J b ν hν htail W
      (fun u hu => hW u u.property (fun hz => hu (Subtype.ext hz)))
    exact_mod_cast hd
  · obtain ⟨W, hfd, hd, hW⟩ := exists_negative_trial_of_count Q J hJ ν hν hmono hmm
    have hneg : ∀ u ∈ W, u ≠ 0 → Q u < 0 := by
      intro u hu hn
      exact hW ⟨u, hu⟩ (fun hz => hn (congrArg Subtype.val hz))
    rw [← hd]
    exact le_iSup_of_le W (le_iSup_of_le hneg (le_iSup_of_le hfd le_rfl))

end KsIndex.Spectral
