module

public import KsIndexLean.FiniteMinMaxCount
public import KsIndexLean.DiskJacobiMinMax
public import KsIndexLean.FiniteZeroMultiplicity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
  [FiniteDimensional ℂ (WeightedDiskAmbient D)]
local instance diskFiniteNonpositiveInner : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

lemma disk_finite_nonpositive_dimension_le (W : Submodule ℂ D) [FiniteDimensional ℂ W]
    (hW : ∀ u : W, (weakJacobi V (u : D) (u : D)).re ≤ 0) :
    Module.finrank ℂ W ≤ (diskSpectralData D V).finiteWeakCount (V.C + 1) 0 := by
  apply finite_nonpositive_trial_dimension_le_count
    (fun u : D => (weakJacobi V u u).re) (weightedDiskAmbientEmbedding D)
    ((diskSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).finiteReciprocalShift_monotone (V.C + 1))
    (fun W _ => trial_dimension_le_ambient (H := WeightedDiskAmbient D) (weightedDiskAmbientEmbedding D)
      (weightedDiskAmbientEmbedding_spec D).1 W)
    (diskJacobi_finite_minmax D V) W hW

lemma disk_finite_nonpositive_dimension_attained :
    ∃ W : Submodule ℂ D, FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = (diskSpectralData D V).finiteWeakCount (V.C + 1) 0 ∧
      ∀ u : W, (weakJacobi V (u : D) (u : D)).re ≤ 0 := by
  apply exists_finite_nonpositive_trial_of_count
    (fun u : D => (weakJacobi V u u).re) _ (weightedDiskAmbientEmbedding D)
    ((diskSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).finiteReciprocalShift_monotone (V.C + 1))
    (diskJacobi_finite_minmax D V)
  change (domainJacobiForm D V 0 0).re = 0
  exact congrArg (fun f : D →L[ℂ] ℂ => (f 0).re) (map_zero (domainJacobiForm D V))

end KsIndex.Spectral
