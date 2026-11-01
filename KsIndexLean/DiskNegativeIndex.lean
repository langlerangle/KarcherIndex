module

public import KsIndexLean.DiskNonpositiveCount
public import KsIndexLean.SpectralNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
  [Infinite (diskSpectralData D V).eigenbasisIndex]
local instance diskNegativeIndexInner1 : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

def diskNegativeCount : ℕ :=
  strictSpectralCount ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) 0

lemma diskJacobi_spectral_tail (n : ℕ) (u : D)
    (hu : ∀ i < n, inner ℂ ((diskSpectralData D V).infiniteEigenbasis i)
      (weightedDiskAmbientEmbedding D u) = 0) :
    (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n *
      ‖weightedDiskAmbientEmbedding D u‖ ^ 2 ≤ (weakJacobi V u u).re := by
  have hs (u v : D) : shiftedDiskForm D V u v = weakJacobi V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedDiskForm_apply D V u v
  have h := @spectral_tail_shifted_lower_bound D (WeightedDiskAmbient D) ℕ
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (shiftedDiskForm_hermitian D V)
    (diskSpectralData D V).infiniteEigenbasis (diskSpectralData D V).infiniteEigenvalues
    (diskSpectralData D V).infiniteEigenvalues_pos (diskSpectralData D V).infiniteEigenvalues_antitone
    (diskSpectralData D V).infiniteEigenbasis_equation
    (fun u v => weakJacobi V u v) (V.C + 1) hs n u hu
  exact h

/-- Actual weighted disk Jacobi negative index equals its negative spectral count. -/
lemma disk_negativeIndex_eq_count :
    KsIndex.NegativeDensity.negativeIndex (fun u : D => (weakJacobi V u u).re) =
      (diskNegativeCount D V : ℕ∞) := by
  exact @negativeIndex_eq_strictSpectralCount D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance inferInstance (fun u : D => (weakJacobi V u u).re)
    (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding_spec D).1
    (diskSpectralData D V).infiniteEigenbasis
    ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((diskSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1))
    (diskJacobi_spectral_tail D V) (diskJacobi_infinite_minmax D V)

end KsIndex.Spectral
