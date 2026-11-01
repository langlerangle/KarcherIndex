module

public import KsIndexLean.SlitEigenvalueBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

/-- Dirichlet comparison with exactly the paper's common hemisphere character. -/
def paperSlitDirichletCharacterDomain (j : ℕ) : Submodule ℂ DiskPairH1 :=
  slitDirichletDomain 3 ⊓ pairCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)

/-- Neumann comparison with exactly the same character as the phase domain. -/
def paperSlitNeumannCharacterDomain (j : ℕ) : Submodule ℂ DiskPairH1 :=
  slitNeumannDomain 3 ⊓ pairCharacterDomain (-(2 * Real.pi) / 3) (KsIndex.FormIndex.zeta 3 ^ j)

lemma isClosed_paperSlitDirichletCharacterDomain (j : ℕ) :
    IsClosed (paperSlitDirichletCharacterDomain j : Set DiskPairH1) :=
  (isClosed_slitDirichletDomain 3).inter (isClosed_pairCharacterDomain _ _)

lemma isClosed_paperSlitNeumannCharacterDomain (j : ℕ) :
    IsClosed (paperSlitNeumannCharacterDomain j : Set DiskPairH1) :=
  (isClosed_slitNeumannDomain 3).inter (isClosed_pairCharacterDomain _ _)

instance paperSlitDirichletCharacterFinite_complete (j : ℕ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (paperSlitDirichletCharacterDomain j))) :=
  finiteH1Domain_completeSpace _
    (pairFiniteDomain_closed _ (isClosed_paperSlitDirichletCharacterDomain j))

instance paperSlitNeumannCharacterFinite_complete (j : ℕ) :
    CompleteSpace (finiteH1Domain (pairFiniteDomain (paperSlitNeumannCharacterDomain j))) :=
  finiteH1Domain_completeSpace _
    (pairFiniteDomain_closed _ (isClosed_paperSlitNeumannCharacterDomain j))

lemma paperSlitDirichletCharacter_le_phase (α : ℝ) (j : ℕ) :
    paperSlitDirichletCharacterDomain j ≤ paperSlitCharacterDomain α j := by
  intro u hu
  exact ⟨slitDirichlet_le_phase 3 _ hu.1, hu.2⟩

lemma paperSlitCharacter_le_Neumann (α : ℝ) (j : ℕ) :
    paperSlitCharacterDomain α j ≤ paperSlitNeumannCharacterDomain j := by
  intro u hu
  exact ⟨slitPhase_le_Neumann 3 _ hu.1, hu.2⟩

/-- Ordered Neumann <= phase <= Dirichlet bracketing on the actual slit domains.
The spectral dimension hypotheses are explicit; no sector is presumed infinite. -/
lemma paperSlitCharacter_infinite_eigenvalue_bracket (α : ℝ) (j : ℕ) (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V).eigenbasisIndex]
    (n : ℕ) :
    (finiteSpectralData (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V).infiniteReciprocalShift (V.C + 1) n ≤
      (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).infiniteReciprocalShift (V.C + 1) n ∧
    (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).infiniteReciprocalShift (V.C + 1) n ≤
      (finiteSpectralData (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V).infiniteReciprocalShift (V.C + 1) n :=
  ⟨finiteCopy_infinite_eigenvalue_le _ _ V (pairFiniteDomain_mono (paperSlitCharacter_le_Neumann α j)) n,
   finiteCopy_infinite_eigenvalue_le _ _ V (pairFiniteDomain_mono (paperSlitDirichletCharacter_le_phase α j)) n⟩

lemma paperSlitCharacter_finite_eigenvalue_bracket (α : ℝ) (j : ℕ) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitDirichletCharacterDomain j)))]
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j)))]
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitNeumannCharacterDomain j)))]
    (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitDirichletCharacterDomain j))))
    (hP : n < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitCharacterDomain α j))))
    (hN : n < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (paperSlitNeumannCharacterDomain j)))) :
    (finiteSpectralData (pairFiniteDomain (paperSlitNeumannCharacterDomain j)) V).finiteReciprocalShift (V.C + 1) ⟨n, hN⟩ ≤
      (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).finiteReciprocalShift (V.C + 1) ⟨n, hP⟩ ∧
    (finiteSpectralData (pairFiniteDomain (paperSlitCharacterDomain α j)) V).finiteReciprocalShift (V.C + 1) ⟨n, hP⟩ ≤
      (finiteSpectralData (pairFiniteDomain (paperSlitDirichletCharacterDomain j)) V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ :=
  ⟨finiteCopy_finite_eigenvalue_le _ _ V (pairFiniteDomain_mono (paperSlitCharacter_le_Neumann α j)) n hP hN,
   finiteCopy_finite_eigenvalue_le _ _ V (pairFiniteDomain_mono (paperSlitDirichletCharacter_le_phase α j)) n hD hP⟩

end KsIndex.Spectral
