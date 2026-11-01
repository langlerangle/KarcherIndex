module

public import KsIndexLean.OrderedSpectralCounts
public import KsIndexLean.InfiniteFormMinMax

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Filter

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Min-max bounds the dimension of every nonpositive trial space by the
nonpositive eigenvalue count, including all zero eigenvalues. -/
lemma nonpositive_trial_dimension_le_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (ν : ℕ → ℝ)
    (hν : Tendsto ν atTop atTop) (hmono : Monotone ν)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (hW : ∀ u : W, Q u ≤ 0) :
    Module.finrank ℂ W ≤ weakSpectralCount ν hν 0 := by
  by_contra hd
  have hpos : 0 < Module.finrank ℂ W := by omega
  have hval : ν (Module.finrank ℂ W - 1) ≤ 0 := (hmm _ 0).mpr
    ⟨W, inferInstance, by omega, fun u => by simpa using hW u⟩
  have hc := (le_level_iff_lt_weakSpectralCount ν hν hmono 0 _).mp hval
  omega

/-- The nonpositive eigenvalue count is attained by a nonpositive trial space. -/
lemma exists_nonpositive_trial_of_count
    (Q : E → ℝ) (hQ : Q 0 = 0) (J : E →L[ℂ] H) (ν : ℕ → ℝ)
    (hν : Tendsto ν atTop atTop) (hmono : Monotone ν)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = weakSpectralCount ν hν 0 ∧ ∀ u : W, Q u ≤ 0 := by
  by_cases hc : weakSpectralCount ν hν 0 = 0
  · refine ⟨⊥, inferInstance, by simp [hc], ?_⟩
    intro u
    have hu : (u : E) = 0 := u.property
    simp [hu, hQ]
  · have hn : weakSpectralCount ν hν 0 - 1 < weakSpectralCount ν hν 0 := by omega
    have hv := (le_level_iff_lt_weakSpectralCount ν hν hmono 0 _).mpr hn
    obtain ⟨W, hW, hd, hu⟩ := (hmm _ 0).mp hv
    exact ⟨W, hW, by omega, fun u => by simpa using hu u⟩

end KsIndex.Spectral
