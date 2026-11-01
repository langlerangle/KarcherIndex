module

public import KsIndexLean.DiskFiniteNonpositiveCount
public import KsIndexLean.FiniteNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
  [FiniteDimensional ℂ (WeightedDiskAmbient D)]
local instance diskFiniteNegativeIndexInner : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

lemma diskJacobi_finite_spectral_tail (n : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) (u : D)
    (hu : ∀ i < n, inner ℂ ((diskSpectralData D V).finiteEigenbasis.toHilbertBasis i)
      (weightedDiskAmbientEmbedding D u) = 0) :
    (diskSpectralData D V).finiteReciprocalShift (V.C + 1) n *
      ‖weightedDiskAmbientEmbedding D u‖ ^ 2 ≤ (weakJacobi V u u).re := by
  have hs (u v : D) : shiftedDiskForm D V u v = weakJacobi V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedDiskForm_apply D V u v
  have hb (i : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) :
      (diskSpectralData D V).operator ((diskSpectralData D V).finiteEigenbasis.toHilbertBasis i) =
        ((diskSpectralData D V).finiteEigenvalues i : ℂ) •
          (diskSpectralData D V).finiteEigenbasis.toHilbertBasis i := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using (diskSpectralData D V).finiteEigenbasis_equation i
  have h := @spectral_tail_shifted_lower_bound D (WeightedDiskAmbient D) (Fin (Module.finrank ℂ (WeightedDiskAmbient D)))
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (shiftedDiskForm_hermitian D V)
    (diskSpectralData D V).finiteEigenbasis.toHilbertBasis (diskSpectralData D V).finiteEigenvalues
    (diskSpectralData D V).finiteEigenvalues_pos (diskSpectralData D V).finiteEigenvalues_antitone
    hb
    (fun u v => weakJacobi V u v) (V.C + 1) hs n u hu
  exact h

/-- Finite-sector actual weighted Jacobi index, including empty sectors. -/
lemma disk_negativeIndex_eq_finite_count :
    KsIndex.NegativeDensity.negativeIndex (fun u : D => (weakJacobi V u u).re) =
      ((diskSpectralData D V).finiteStrictCount (V.C + 1) 0 : ℕ∞) := by
  exact @negativeIndex_eq_finite_strict_count D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance inferInstance
    (Module.finrank ℂ (WeightedDiskAmbient D))
    (fun u : D => (weakJacobi V u u).re)
    (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding_spec D).1
    (diskSpectralData D V).finiteEigenbasis.toHilbertBasis
    ((diskSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).finiteReciprocalShift_monotone (V.C + 1))
    (fun W _ => trial_dimension_le_ambient (H := WeightedDiskAmbient D)
      (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding_spec D).1 W)
    (diskJacobi_finite_spectral_tail D V) (diskJacobi_finite_minmax D V)

end KsIndex.Spectral
