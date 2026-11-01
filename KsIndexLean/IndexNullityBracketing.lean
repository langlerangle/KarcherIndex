module

public import KsIndexLean.FiniteCountBracketing
public import KsIndexLean.JacobiRadicalCounts

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Dimension of the full weak Jacobi radical, not a smooth-kernel assertion. -/
def finiteCopyWeakNullity {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) : ℕ :=
  Module.finrank ℂ (@formRadical (finiteH1Domain D) inferInstance
    (finiteH1Domain_innerProductSpace D) (finiteJacobiForm D V))

/-- Variational index plus the full weak nullity. -/
def finiteCopyIndexNullity {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) (V : BoundedRealPotential) : ℕ∞ :=
  KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) +
    (finiteCopyWeakNullity D V : ℕ∞)

lemma finiteCopy_indexNullity_infinite {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) [Infinite (finiteSpectralData D V).eigenbasisIndex] :
    finiteCopyIndexNullity D V = (finiteCopyNonpositiveCount D V : ℕ∞) := by
  have hle : finiteCopyNegativeCount D V ≤ finiteCopyNonpositiveCount D V :=
    strictSpectralCount_le_weakSpectralCount _ _ 0
  have he := finiteCopyRadical_finrank_eq_count D V
  change finiteCopyWeakNullity D V = _ at he
  have hn : finiteCopyNegativeCount D V + finiteCopyWeakNullity D V =
      finiteCopyNonpositiveCount D V := by omega
  unfold finiteCopyIndexNullity
  rw [finiteCopy_negativeIndex_eq_count]
  exact_mod_cast hn

lemma finiteCopy_indexNullity_finite {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) [FiniteDimensional ℂ (WeightedFiniteAmbient D)] :
    finiteCopyIndexNullity D V = ((finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 : ℕ∞) := by
  classical
  have hle : (finiteSpectralData D V).finiteStrictCount (V.C + 1) 0 ≤
      (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 := by
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  have he := finiteCopyRadical_finrank_eq_finite_count D V
  change finiteCopyWeakNullity D V = _ at he
  have hn : (finiteSpectralData D V).finiteStrictCount (V.C + 1) 0 + finiteCopyWeakNullity D V =
      (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 := by omega
  unfold finiteCopyIndexNullity
  rw [finiteCopy_negativeIndex_eq_finite_count]
  exact_mod_cast hn

lemma finiteCopy_finite_indexNullity_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] [FiniteDimensional ℂ (WeightedFiniteAmbient F)] :
    finiteCopyIndexNullity D V ≤ finiteCopyIndexNullity F V := by
  rw [finiteCopy_indexNullity_finite D V, finiteCopy_indexNullity_finite F V]
  exact_mod_cast finiteCopy_finite_nonpositive_count_le D F V h

lemma finiteCopy_finite_to_infinite_indexNullity_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedFiniteAmbient D)] [Infinite (finiteSpectralData F V).eigenbasisIndex] :
    finiteCopyIndexNullity D V ≤ finiteCopyIndexNullity F V := by
  rw [finiteCopy_indexNullity_finite D V, finiteCopy_indexNullity_infinite F V]
  exact_mod_cast finiteCopy_finite_to_infinite_nonpositive_count_le D F V h

lemma finiteCopy_infinite_to_finite_indexNullity_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex] [FiniteDimensional ℂ (WeightedFiniteAmbient F)] :
    finiteCopyIndexNullity D V ≤ finiteCopyIndexNullity F V := by
  rw [finiteCopy_indexNullity_infinite D V, finiteCopy_indexNullity_finite F V]
  exact_mod_cast finiteCopy_infinite_to_finite_nonpositive_count_le D F V h

lemma finiteCopy_infinite_indexNullity_le {ι : Type*} [Fintype ι]
    (D F : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] [CompleteSpace (finiteH1Domain F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (finiteSpectralData D V).eigenbasisIndex] [Infinite (finiteSpectralData F V).eigenbasisIndex] :
    finiteCopyIndexNullity D V ≤ finiteCopyIndexNullity F V := by
  rw [finiteCopy_indexNullity_infinite D V, finiteCopy_indexNullity_infinite F V]
  exact_mod_cast (finiteCopy_infinite_count_le D F V h 0).2


lemma paperSlitCharacter_finite_indexNullity_bracket (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitDirichletCharacterDomain j)))]
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j)))]
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitNeumannCharacterDomain j)))]
    : finiteCopyIndexNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V ≤ finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V ∧
      finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V ≤ finiteCopyIndexNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V :=
  ⟨finiteCopy_finite_indexNullity_le _ _ V
      (pairFiniteDomain_mono (paperSlitDirichletCharacter_le_phase α j)),
   finiteCopy_finite_indexNullity_le _ _ V
      (pairFiniteDomain_mono (paperSlitCharacter_le_Neumann α j))⟩

lemma paperSlitCharacter_infinite_indexNullity_bracket (α : ℝ) (j : ℕ)
    (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V).eigenbasisIndex]
    : finiteCopyIndexNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V ≤ finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V ∧
      finiteCopyIndexNullity (pairFiniteDomain (paperSlitCharacterDomain α j)) V ≤ finiteCopyIndexNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V :=
  ⟨finiteCopy_infinite_indexNullity_le _ _ V
      (pairFiniteDomain_mono (paperSlitDirichletCharacter_le_phase α j)),
   finiteCopy_infinite_indexNullity_le _ _ V
      (pairFiniteDomain_mono (paperSlitCharacter_le_Neumann α j))⟩

end KsIndex.Spectral
