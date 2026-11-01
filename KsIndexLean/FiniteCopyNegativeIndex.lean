module

public import KsIndexLean.FiniteCopyNonpositiveCount
public import KsIndexLean.SpectralNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
  [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
  [Infinite (finiteSpectralData D V).eigenbasisIndex]
local instance finiteCopyNegativeIndexInner1 : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

def finiteCopyNegativeCount : ℕ :=
  strictSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) 0

lemma finiteCopyJacobi_spectral_tail (n : ℕ) (u : finiteH1Domain D)
    (hu : ∀ i < n, inner ℂ ((finiteSpectralData D V).infiniteEigenbasis i)
      (finiteH1WeightedValue D u) = 0) :
    (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n *
      ‖finiteH1WeightedValue D u‖ ^ 2 ≤ (finiteH1Jacobi D V u u).re := by
  have hs (u v : finiteH1Domain D) : shiftedFiniteForm D V u v = finiteH1Jacobi D V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedFiniteForm_apply D V u v
  have h := @spectral_tail_shifted_lower_bound (finiteH1Domain D) (WeightedFiniteAmbient D) ℕ
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (shiftedFiniteForm_hermitian D V)
    (finiteSpectralData D V).infiniteEigenbasis (finiteSpectralData D V).infiniteEigenvalues
    (finiteSpectralData D V).infiniteEigenvalues_pos (finiteSpectralData D V).infiniteEigenvalues_antitone
    (finiteSpectralData D V).infiniteEigenbasis_equation
    (fun u v => finiteH1Jacobi D V u v) (V.C + 1) hs n u hu
  exact h

/-- Actual weighted finite-copy Jacobi negative index equals its negative spectral count. -/
lemma finiteCopy_negativeIndex_eq_count :
    KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) =
      (finiteCopyNegativeCount D V : ℕ∞) := by
  exact @negativeIndex_eq_strictSpectralCount (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance inferInstance (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re)
    (finiteH1WeightedValue D) (finiteH1WeightedValue_spec D).1
    (finiteSpectralData D V).infiniteEigenbasis
    ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1))
    (finiteCopyJacobi_spectral_tail D V) (finiteCopyJacobi_infinite_minmax D V)

end KsIndex.Spectral
