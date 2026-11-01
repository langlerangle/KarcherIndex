module

public import KsIndexLean.MixedKernelExtension
public import KsIndexLean.DirichletCharacterKernels

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1

/-- The slit Neumann zero character has no weak Jacobi kernel. -/
lemma three_slitNeumann_zero_nullity :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain 0))
      (surfacePotential 3) = 0 := by
  rw [paperSlitNeumannCharacter_nullity, paperHemisphere_zero_nullity,
    paperNeumannOdd_nullity_zero (by decide), add_zero]

/-- Each nontrivial slit Neumann character has exactly one weak kernel dimension. -/
lemma three_slitNeumann_nontrivial_nullity {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j))
      (surfacePotential 3) = 1 := by
  rw [paperSlitNeumannCharacter_nullity, paperNeumannOdd_nullity_zero hj, add_zero]
  interval_cases j
  · contradiction
  · exact paperHemisphere_one_nullity
  · exact paperHemisphere_two_nullity

/-- The slit Dirichlet zero character has exactly one weak kernel dimension. -/
lemma three_slitDirichlet_zero_nullity :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain 0))
      (surfacePotential 3) = 1 := by
  rw [paperSlitDirichletCharacter_nullity, paperDirichletEven_nullity_zero (by decide),
    paperDirichletOddCharacter_zero_nullity, zero_add]

/-- Nontrivial slit Dirichlet characters have no weak Jacobi kernel. -/
lemma three_slitDirichlet_nontrivial_nullity {j : ℕ} (hj : j < 3) (hj0 : j ≠ 0) :
    finiteCopyWeakNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j))
      (surfacePotential 3) = 0 := by
  rw [paperSlitDirichletCharacter_nullity, paperDirichletEven_nullity_zero hj,
    paperDirichletOddCharacter_nontrivial_nullity j (by omega), zero_add]

lemma three_slitNeumann_index_add_nullity {j : ℕ} (hj : j < 3) :
    pairWeakIndex (paperSlitNeumannCharacterDomain j) (surfacePotential 3) +
      (finiteCopyWeakNullity (pairFiniteDomain (paperSlitNeumannCharacterDomain j))
        (surfacePotential 3) : ℕ∞) = if j = 0 then 2 else 3 := by
  rw [three_slitNeumann_index_two hj]
  by_cases h : j = 0
  · subst j
    rw [three_slitNeumann_zero_nullity]
    norm_num
  · rw [three_slitNeumann_nontrivial_nullity hj h]
    norm_num [h]

lemma three_slitDirichlet_index_add_nullity {j : ℕ} (hj : j < 3) :
    pairWeakIndex (paperSlitDirichletCharacterDomain j) (surfacePotential 3) +
      (finiteCopyWeakNullity (pairFiniteDomain (paperSlitDirichletCharacterDomain j))
        (surfacePotential 3) : ℕ∞) = if j = 0 then 2 else 1 := by
  rw [three_slitDirichlet_index_one hj]
  by_cases h : j = 0
  · subst j
    rw [three_slitDirichlet_zero_nullity]
    norm_num
  · rw [three_slitDirichlet_nontrivial_nullity hj h]
    norm_num [h]

end KsIndex.Spectral
