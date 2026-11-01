module

public import KsIndexLean.GeneralDirichletPositivity
public import KsIndexLean.PositiveMinMax

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.FormIndex KsIndex.Spherical

/-- All ordered Dirichlet eigenvalues in a nontrivial character are positive.
This version covers an infinite sector. -/
lemma generalDirichlet_infinite_eigenvalue_positive {k j : ℕ}
    (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    [Infinite (diskSpectralData (mixedCharacterDomain k j false false)
      (surfacePotential k)).eigenbasisIndex] (n : ℕ) :
    0 < (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).infiniteReciprocalShift ((surfacePotential k).C + 1) n :=
  diskJacobi_infinite_positive_of_positive _ _
    (generalDirichlet_character_positive_of_range hk hj0 hjk) n

/-- Finite sectors retain their actual eigenvalue index type. -/
lemma generalDirichlet_finite_eigenvalue_positive {k j : ℕ}
    (hk : 3 ≤ k) (hj0 : 0 < j) (hjk : j < k)
    [FiniteDimensional ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false))]
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient (mixedCharacterDomain k j false false)))) :
    0 < (diskSpectralData (mixedCharacterDomain k j false false) (surfacePotential k)).finiteReciprocalShift ((surfacePotential k).C + 1) n :=
  diskJacobi_finite_positive_of_positive _ _
    (generalDirichlet_character_positive_of_range hk hj0 hjk) n

end KsIndex.Spectral
