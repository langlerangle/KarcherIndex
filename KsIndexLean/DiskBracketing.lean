module

public import KsIndexLean.VariationalBracketing

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

/-- Enlarging a disk form domain lowers each available ordered eigenvalue.
This first instance treats infinite sectors; finite alternatives follow separately. -/
lemma disk_infinite_eigenvalue_le 
    (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (diskSpectralData D V).eigenbasisIndex]
    [Infinite (diskSpectralData F V).eigenbasisIndex] (n : ℕ) :
    (diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n ≤
      (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n := by
  exact eigenvalue_le_of_trial_inclusion (Submodule.inclusion h)
    (Submodule.inclusion_injective h)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding D u‖ ^ 2)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (diskJacobi_infinite_minmax D V n)
    (diskJacobi_infinite_minmax F V n)

lemma disk_finite_eigenvalue_le 
    (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    [FiniteDimensional ℂ (WeightedDiskAmbient F)] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient D))
    (hF : n < Module.finrank ℂ (WeightedDiskAmbient F)) :
    (diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ ≤
      (diskSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ := by
  exact eigenvalue_le_of_trial_inclusion (Submodule.inclusion h)
    (Submodule.inclusion_injective h)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding D u‖ ^ 2)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (diskJacobi_finite_minmax D V ⟨n, hD⟩)
    (diskJacobi_finite_minmax F V ⟨n, hF⟩)

lemma disk_finite_to_infinite_eigenvalue_le 
    (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    [Infinite (diskSpectralData F V).eigenbasisIndex] (n : ℕ)
    (hD : n < Module.finrank ℂ (WeightedDiskAmbient D)) :
    (diskSpectralData F V).infiniteReciprocalShift (V.C + 1) n ≤
      (diskSpectralData D V).finiteReciprocalShift (V.C + 1) ⟨n, hD⟩ := by
  exact eigenvalue_le_of_trial_inclusion (Submodule.inclusion h)
    (Submodule.inclusion_injective h)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding D u‖ ^ 2)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (diskJacobi_finite_minmax D V ⟨n, hD⟩)
    (diskJacobi_infinite_minmax F V n)

lemma disk_infinite_to_finite_eigenvalue_le 
    (D F : Submodule ℂ ComplexH1)
    [CompleteSpace (D)] [CompleteSpace (F)]
    (V : BoundedRealPotential) (h : D ≤ F)
    [Infinite (diskSpectralData D V).eigenbasisIndex]
    [FiniteDimensional ℂ (WeightedDiskAmbient F)] (n : ℕ)
    (hF : n < Module.finrank ℂ (WeightedDiskAmbient F)) :
    (diskSpectralData F V).finiteReciprocalShift (V.C + 1) ⟨n, hF⟩ ≤
      (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n := by
  exact eigenvalue_le_of_trial_inclusion (Submodule.inclusion h)
    (Submodule.inclusion_injective h)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding D u‖ ^ 2)
    (fun u => (weakJacobi V u u).re)
    (fun u => ‖weightedDiskAmbientEmbedding F u‖ ^ 2)
    (fun _ => rfl) (fun _ => rfl) (n + 1) _ _
    (diskJacobi_infinite_minmax D V n)
    (diskJacobi_finite_minmax F V ⟨n, hF⟩)

end KsIndex.Spectral
