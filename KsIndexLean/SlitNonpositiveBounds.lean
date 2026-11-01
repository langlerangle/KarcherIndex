module

public import KsIndexLean.SlitKernelRepresentatives

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Index-plus-nullity monotonicity without a dimension hypothesis: all four
finite/infinite cases are discharged internally. -/
lemma finiteCopy_indexNullity_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F) :
    finiteCopyIndexNullity D V ≤ finiteCopyIndexNullity F V := by
  by_cases hd : FiniteDimensional ℂ (WeightedFiniteAmbient D)
  · let := hd
    by_cases hf : FiniteDimensional ℂ (WeightedFiniteAmbient F)
    · let := hf
      exact finiteCopy_finite_indexNullity_le D F V h
    · let := (finiteSpectralData F V).eigenbasisIndex_infinite hf
      exact finiteCopy_finite_to_infinite_indexNullity_le D F V h
  · let := (finiteSpectralData D V).eigenbasisIndex_infinite hd
    by_cases hf : FiniteDimensional ℂ (WeightedFiniteAmbient F)
    · let := hf
      exact finiteCopy_infinite_to_finite_indexNullity_le D F V h
    · let := (finiteSpectralData F V).eigenbasisIndex_infinite hf
      exact finiteCopy_infinite_indexNullity_le D F V h

lemma paperSlitCharacter_indexNullity_bracket (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential) :
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V ≤
      finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V ∧
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V ≤
      finiteCopyIndexNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V :=
  ⟨finiteCopy_indexNullity_le _ _ V
      (pairFiniteDomain_mono (paperSlitDirichletCharacter_le_phase α j)),
    finiteCopy_indexNullity_le _ _ V
      (pairFiniteDomain_mono (paperSlitCharacter_le_Neumann α j))⟩

/-- Rotation character zero has exactly two nonpositive dimensions for every phase.
This count alone does not distinguish negative directions from the kernel. -/
lemma three_paperSlit_zero_index_add_nullity (α : ℝ) :
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α 0))
      (surfacePotential 3) = 2 := by
  obtain ⟨hlo, hhi⟩ := paperSlitCharacter_indexNullity_bracket α 0 (surfacePotential 3)
  have hd := three_slitDirichlet_index_add_nullity (by decide : 0 < 3)
  have hn := three_slitNeumann_index_add_nullity (by decide : 0 < 3)
  change finiteCopyIndexNullity _ _ = _ at hd hn
  rw [hd] at hlo
  rw [hn] at hhi
  exact le_antisymm hhi hlo

lemma three_paperSlit_nontrivial_index_add_nullity_le_three
    (α : ℝ) {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j))
      (surfacePotential 3) ≤ 3 := by
  have h := (paperSlitCharacter_indexNullity_bracket α j (surfacePotential 3)).2
  have hn := three_slitNeumann_index_add_nullity hj
  change finiteCopyIndexNullity _ _ = _ at hn
  rw [if_neg hj0] at hn
  exact h.trans_eq hn

end KsIndex.Spectral
