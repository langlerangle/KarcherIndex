module

public import KsIndexLean.FiniteFormMinMax

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

/-- A monotone finite list has exactly an initial segment below a threshold. -/
lemma finite_le_iff_lt_count {m : ℕ} (ν : Fin m → ℝ) (hm : Monotone ν)
    (L : ℝ) (i : Fin m) :
    ν i ≤ L ↔ i.val < (Finset.univ.filter fun j => ν j ≤ L).card := by
  classical
  constructor
  · intro hi
    have hs : Finset.Iic i ⊆ (Finset.univ.filter fun j => ν j ≤ L) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hm (Finset.mem_Iic.mp hj)).trans hi⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    omega
  · intro hc
    by_contra hi
    have hs : (Finset.univ.filter fun j => ν j ≤ L) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have h := (hm (le_of_not_gt hji)).trans (Finset.mem_filter.mp hj).2
      exact hi h
    have hd := Finset.card_le_card hs
    rw [Fin.card_Iio] at hd
    omega

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H] {m : ℕ}

lemma trial_dimension_le_ambient [FiniteDimensional ℂ H]
    (J : E →L[ℂ] H) (hJ : Function.Injective J) (W : Submodule ℂ E) :
    Module.finrank ℂ W ≤ Module.finrank ℂ H := by
  exact LinearMap.finrank_le_finrank_of_injective
    (f := J.toLinearMap.comp W.subtype) (hJ.comp Subtype.val_injective)

/-- The ambient dimension bound handles the finite list's endpoint, including
sectors with no positive eigenvalue. -/
lemma finite_nonpositive_trial_dimension_le_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (ν : Fin m → ℝ) (hm : Monotone ν)
    (hdim : ∀ W : Submodule ℂ E, FiniteDimensional ℂ W → Module.finrank ℂ W ≤ m)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (hW : ∀ u : W, Q u ≤ 0) :
    Module.finrank ℂ W ≤ (Finset.univ.filter fun i => ν i ≤ 0).card := by
  classical
  by_contra hc
  have hd := hdim W inferInstance
  have hp : 0 < Module.finrank ℂ W := by omega
  let n : Fin m := ⟨Module.finrank ℂ W - 1, by omega⟩
  have hv : ν n ≤ 0 := (hmm n 0).mpr
    ⟨W, inferInstance, by dsimp [n]; omega, fun u => by simpa using hW u⟩
  have hh := (finite_le_iff_lt_count ν hm 0 n).mp hv
  dsimp [n] at hh
  omega

lemma exists_finite_nonpositive_trial_of_count
    (Q : E → ℝ) (hQ : Q 0 = 0) (J : E →L[ℂ] H)
    (ν : Fin m → ℝ) (hm : Monotone ν)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = (Finset.univ.filter fun i => ν i ≤ 0).card ∧
      ∀ u : W, Q u ≤ 0 := by
  classical
  let k := (Finset.univ.filter fun i => ν i ≤ 0).card
  have hk : k ≤ m := by
    simpa [k] using Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i => ν i ≤ 0)
  by_cases hz : k = 0
  · refine ⟨⊥, inferInstance, by change Module.finrank ℂ (⊥ : Submodule ℂ E) = k; rw [finrank_bot, hz], ?_⟩
    intro u
    have hu : (u : E) = 0 := u.property
    simp [hu, hQ]
  · let n : Fin m := ⟨k - 1, by omega⟩
    have hv : ν n ≤ 0 := (finite_le_iff_lt_count ν hm 0 n).mpr (by change k - 1 < k; omega)
    obtain ⟨W, hfd, hd, hW⟩ := (hmm n 0).mp hv
    refine ⟨W, hfd, ?_, fun u => by simpa using hW u⟩
    change Module.finrank ℂ W = k
    dsimp [n] at hd
    omega

end KsIndex.Spectral
