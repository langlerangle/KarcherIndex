module

public import KsIndexLean.FiniteCopyBracketing
public import KsIndexLean.SlitComparisonSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.Trace KsIndex.WeakH1 KsIndex.Spherical

lemma pairFiniteDomain_mono {D F : Submodule ℂ DiskPairH1} (h : D ≤ F) :
    pairFiniteDomain D ≤ pairFiniteDomain F := fun _ hu => h hu

/-- Ordered Neumann <= phase <= Dirichlet bracketing on the actual slit domains.
The spectral dimension hypotheses are explicit; no sector is presumed infinite. -/
lemma slit_infinite_eigenvalue_bracket (k : ℕ) (phase : ℂ) (V : BoundedRealPotential)
    [Infinite (finiteSpectralData (pairFiniteDomain (slitDirichletDomain k)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (slitTraceDomain k phase)) V).eigenbasisIndex]
    [Infinite (finiteSpectralData (pairFiniteDomain (slitNeumannDomain k)) V).eigenbasisIndex]
    (n : ℕ) :
    (finiteSpectralData (pairFiniteDomain (slitNeumannDomain k)) V).infiniteReciprocalShift (V.C + 1) n ≤
      (finiteSpectralData (pairFiniteDomain (slitTraceDomain k phase)) V).infiniteReciprocalShift (V.C + 1) n ∧
    (finiteSpectralData (pairFiniteDomain (slitTraceDomain k phase)) V).infiniteReciprocalShift (V.C + 1) n ≤
      (finiteSpectralData (pairFiniteDomain (slitDirichletDomain k)) V).infiniteReciprocalShift (V.C + 1) n :=
  ⟨finiteCopy_infinite_eigenvalue_le _ _ V (pairFiniteDomain_mono (slitPhase_le_Neumann k phase)) n,
   finiteCopy_infinite_eigenvalue_le _ _ V (pairFiniteDomain_mono (slitDirichlet_le_phase k phase)) n⟩

lemma slit_finite_eigenvalue_bracket (k : ℕ) (phase : ℂ) (V : BoundedRealPotential)
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (slitDirichletDomain k)))]
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (slitTraceDomain k phase)))]
    [FiniteDimensional ℂ (WeightedFiniteAmbient (pairFiniteDomain (slitNeumannDomain k)))]
    (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (slitDirichletDomain k))))
    (hP : n < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (slitTraceDomain k phase))))
    (hN : n < Module.finrank ℂ (WeightedFiniteAmbient (pairFiniteDomain (slitNeumannDomain k)))) :
    (finiteSpectralData (pairFiniteDomain (slitNeumannDomain k)) V).finiteReciprocalShift (V.C + 1) ⟨n, hN⟩ ≤
      (finiteSpectralData (pairFiniteDomain (slitTraceDomain k phase)) V).finiteReciprocalShift (V.C + 1) ⟨n, hP⟩ ∧
    (finiteSpectralData (pairFiniteDomain (slitTraceDomain k phase)) V).finiteReciprocalShift (V.C + 1) ⟨n, hP⟩ ≤
      (finiteSpectralData (pairFiniteDomain (slitDirichletDomain k)) V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ :=
  ⟨finiteCopy_finite_eigenvalue_le _ _ V (pairFiniteDomain_mono (slitPhase_le_Neumann k phase)) n hP hN,
   finiteCopy_finite_eigenvalue_le _ _ V (pairFiniteDomain_mono (slitDirichlet_le_phase k phase)) n hD hP⟩

end KsIndex.Spectral
