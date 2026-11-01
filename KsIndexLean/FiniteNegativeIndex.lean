module

public import KsIndexLean.FiniteMinMaxCount
public import KsIndexLean.SpectralNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

lemma finite_lt_iff_lt_count {m : ℕ} (ν : Fin m → ℝ) (hm : Monotone ν)
    (L : ℝ) (i : Fin m) :
    ν i < L ↔ i.val < (Finset.univ.filter fun j => ν j < L).card := by
  classical
  constructor
  · intro hi
    have hs : Finset.Iic i ⊆ (Finset.univ.filter fun j => ν j < L) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hm (Finset.mem_Iic.mp hj)).trans_lt hi⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    omega
  · intro hc
    by_contra hi
    have hs : (Finset.univ.filter fun j => ν j < L) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      exact hi ((hm (le_of_not_gt hji)).trans_lt (Finset.mem_filter.mp hj).2)
    have hd := Finset.card_le_card hs
    rw [Fin.card_Iio] at hd
    omega

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] {m : ℕ}

lemma finite_negative_trial_dimension_le_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (b : Fin m → H) (ν : Fin m → ℝ) (hm : Monotone ν)
    (hdim : ∀ W : Submodule ℂ E, FiniteDimensional ℂ W → Module.finrank ℂ W ≤ m)
    (htail : ∀ n u, (∀ i < n, inner ℂ (b i) (J u) = 0) → ν n * ‖J u‖ ^ 2 ≤ Q u)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W] (hW : ∀ u : W, u ≠ 0 → Q u < 0) :
    Module.finrank ℂ W ≤ (Finset.univ.filter fun i => ν i < 0).card := by
  classical
  by_contra hd
  let k := (Finset.univ.filter fun i => ν i < 0).card
  have hdimW := hdim W inferInstance
  let n : Fin m := ⟨k, by omega⟩
  let f : Fin k → Fin m := fun i => ⟨i.val, by omega⟩
  obtain ⟨u, hu, horth⟩ := exists_nonzero_orthogonal_in_trial J (fun i => b (f i)) W
    (by simpa using (show k < Module.finrank ℂ W by omega))
  have hn : 0 ≤ ν n := by
    by_contra hn
    have h := (finite_lt_iff_lt_count ν hm 0 n).mp (lt_of_not_ge hn)
    change k < k at h
    omega
  have hlo := htail n u (by
    intro i hi
    have h := horth ⟨i.val, hi⟩
    exact h)
  have hnonneg := mul_nonneg hn (sq_nonneg ‖J u‖)
  have hneg := hW u hu
  linarith

lemma exists_finite_negative_trial_of_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (hJ : Function.Injective J)
    (ν : Fin m → ℝ) (hm : Monotone ν)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2) :
    ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = (Finset.univ.filter fun i => ν i < 0).card ∧
      ∀ u : W, u ≠ 0 → Q u < 0 := by
  classical
  let k := (Finset.univ.filter fun i => ν i < 0).card
  have hk : k ≤ m := by
    simpa [k] using Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i => ν i < 0)
  by_cases hz : k = 0
  · refine ⟨⊥, inferInstance, ?_, ?_⟩
    · change Module.finrank ℂ (⊥ : Submodule ℂ E) = k
      rw [finrank_bot, hz]
    · intro u hu
      exact False.elim (hu (Subsingleton.elim _ _))
  · let n : Fin m := ⟨k - 1, by omega⟩
    have hv : ν n < 0 := (finite_lt_iff_lt_count ν hm 0 n).mpr (by change k - 1 < k; omega)
    obtain ⟨W, hfd, hd, hW⟩ := (hmm n (ν n)).mp le_rfl
    refine ⟨W, hfd, ?_, ?_⟩
    · change Module.finrank ℂ W = k
      dsimp [n] at hd
      omega
    · intro u hu
      have hbulk : J u ≠ 0 := by
        intro he
        exact hu (Subtype.ext (hJ (he.trans J.map_zero.symm)))
      exact (hW u).trans_lt (mul_neg_of_neg_of_pos hv (sq_pos_of_pos (norm_pos_iff.mpr hbulk)))

/-- Finite-sector identification with the repository's existing variational index. -/
lemma negativeIndex_eq_finite_strict_count
    (Q : E → ℝ) (J : E →L[ℂ] H) (hJ : Function.Injective J)
    (b : Fin m → H) (ν : Fin m → ℝ) (hm : Monotone ν)
    (hdim : ∀ W : Submodule ℂ E, FiniteDimensional ℂ W → Module.finrank ℂ W ≤ m)
    (htail : ∀ n u, (∀ i < n, inner ℂ (b i) (J u) = 0) → ν n * ‖J u‖ ^ 2 ≤ Q u)
    (hmm : ∀ n L, ν n ≤ L ↔ ∃ W : Submodule ℂ E, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = n.val + 1 ∧ ∀ u : W, Q u ≤ L * ‖J u‖ ^ 2) :
    KsIndex.NegativeDensity.negativeIndex Q =
      ((Finset.univ.filter fun i => ν i < 0).card : ℕ∞) := by
  apply le_antisymm
  · unfold KsIndex.NegativeDensity.negativeIndex
    refine iSup_le fun W => iSup_le fun hW => iSup_le fun hfd => ?_
    let := hfd
    have hd := finite_negative_trial_dimension_le_count Q J b ν hm hdim htail W
      (fun u hu => hW u u.property (fun hz => hu (Subtype.ext hz)))
    exact_mod_cast hd
  · obtain ⟨W, hfd, hd, hW⟩ := exists_finite_negative_trial_of_count Q J hJ ν hm hmm
    have hneg : ∀ u ∈ W, u ≠ 0 → Q u < 0 := by
      intro u hu hn
      exact hW ⟨u, hu⟩ (fun hz => hn (congrArg Subtype.val hz))
    rw [← hd]
    exact le_iSup_of_le W (le_iSup_of_le hneg (le_iSup_of_le hfd le_rfl))

end KsIndex.Spectral
