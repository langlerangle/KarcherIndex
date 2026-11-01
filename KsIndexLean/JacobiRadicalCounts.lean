module

public import KsIndexLean.JacobiRadicalRealization
public import KsIndexLean.FiniteZeroMultiplicity
public import KsIndexLean.InfiniteZeroMultiplicity
public import KsIndexLean.DiskNegativeIndex
public import KsIndexLean.FiniteCopyNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

lemma diskRadical_finrank_eq_count (D : Submodule ℂ ComplexH1) [CompleteSpace D]
    (V : BoundedRealPotential) [Infinite (diskSpectralData D V).eigenbasisIndex] :
    Module.finrank ℂ (@formRadical D inferInstance (diskDomain_innerProductSpace D)
      (domainJacobiForm D V)) = diskNonpositiveCount D V - diskNegativeCount D V := by
  rw [diskRadical_finrank]
  exact (diskSpectralData D V).infinite_zero_multiplicity (V.C + 1)

lemma finiteCopyRadical_finrank_eq_count {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) [Infinite (finiteSpectralData D V).eigenbasisIndex] :
    Module.finrank ℂ (@formRadical (finiteH1Domain D) inferInstance (finiteH1Domain_innerProductSpace D)
      (finiteJacobiForm D V)) = finiteCopyNonpositiveCount D V - finiteCopyNegativeCount D V := by
  rw [finiteCopyRadical_finrank]
  exact (finiteSpectralData D V).infinite_zero_multiplicity (V.C + 1)

/-- Finite-dimensional disk sectors, including the zero sector. -/
lemma diskRadical_finrank_eq_finite_count (D : Submodule ℂ ComplexH1) [CompleteSpace D]
    (V : BoundedRealPotential) [FiniteDimensional ℂ (WeightedDiskAmbient D)] :
    Module.finrank ℂ (@formRadical D inferInstance (diskDomain_innerProductSpace D)
      (domainJacobiForm D V)) =
      (diskSpectralData D V).finiteWeakCount (V.C + 1) 0 -
      (diskSpectralData D V).finiteStrictCount (V.C + 1) 0 := by
  rw [diskRadical_finrank]
  exact (diskSpectralData D V).finite_zero_multiplicity (V.C + 1)

/-- Finite-dimensional sectors of the finite-copy form; the number of copies
and the dimension of the sector are separate parameters. -/
lemma finiteCopyRadical_finrank_eq_finite_count {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) [FiniteDimensional ℂ (WeightedFiniteAmbient D)] :
    Module.finrank ℂ (@formRadical (finiteH1Domain D) inferInstance
      (finiteH1Domain_innerProductSpace D) (finiteJacobiForm D V)) =
      (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 -
      (finiteSpectralData D V).finiteStrictCount (V.C + 1) 0 := by
  rw [finiteCopyRadical_finrank]
  exact (finiteSpectralData D V).finite_zero_multiplicity (V.C + 1)

end KsIndex.Spectral
