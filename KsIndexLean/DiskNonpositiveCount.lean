module

public import KsIndexLean.DiskJacobiMinMax
public import KsIndexLean.MinMaxNonpositiveCount

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
  [Infinite (diskSpectralData D V).eigenbasisIndex]
local instance diskNonpositiveCountInner1 : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

/-- Number of nonpositive weighted disk Jacobi eigenvalues, with complex multiplicity. -/
def diskNonpositiveCount : ℕ :=
  weakSpectralCount ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) 0

lemma disk_nonpositive_dimension_le (W : Submodule ℂ D) [FiniteDimensional ℂ W]
    (hW : ∀ u : W, (weakJacobi V (u : D) (u : D)).re ≤ 0) :
    Module.finrank ℂ W ≤ diskNonpositiveCount D V := by
  exact nonpositive_trial_dimension_le_count (fun u : D => (weakJacobi V u u).re)
    (weightedDiskAmbientEmbedding D) ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1))
    (diskJacobi_infinite_minmax D V) W hW

lemma disk_nonpositive_count_attained :
    ∃ W : Submodule ℂ D, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = diskNonpositiveCount D V ∧
      ∀ u : W, (weakJacobi V (u : D) (u : D)).re ≤ 0 := by
  have hz : (weakJacobi V (0 : D) (0 : D)).re = 0 := by
    change (domainJacobiForm D V 0 0).re = 0
    exact congrArg (fun f : D →L[ℂ] ℂ => (f 0).re) (map_zero (domainJacobiForm D V))
  exact exists_nonpositive_trial_of_count (fun u : D => (weakJacobi V u u).re) hz
    (weightedDiskAmbientEmbedding D) ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1))
    (diskJacobi_infinite_minmax D V)

end KsIndex.Spectral
