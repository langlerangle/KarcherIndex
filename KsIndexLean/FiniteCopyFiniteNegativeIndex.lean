module

public import KsIndexLean.FiniteCopyFiniteNonpositiveCount
public import KsIndexLean.FiniteNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
  [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
local instance finiteCopyFiniteNegativeIndexInner : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

lemma finiteCopyJacobi_finite_spectral_tail (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) (u : finiteH1Domain D)
    (hu : ∀ i < n, inner ℂ ((finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i)
      (finiteH1WeightedValue D u) = 0) :
    (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) n *
      ‖finiteH1WeightedValue D u‖ ^ 2 ≤ (finiteH1Jacobi D V u u).re := by
  have hs (u v : finiteH1Domain D) : shiftedFiniteForm D V u v = finiteH1Jacobi D V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
    simpa only [finiteJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using shiftedFiniteForm_apply D V u v
  have hb (i : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) :
      (finiteSpectralData D V).operator ((finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i) =
        ((finiteSpectralData D V).finiteEigenvalues i : ℂ) •
          (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using (finiteSpectralData D V).finiteEigenbasis_equation i
  have h := @spectral_tail_shifted_lower_bound (finiteH1Domain D) (WeightedFiniteAmbient D) (Fin (Module.finrank ℂ (WeightedFiniteAmbient D)))
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (shiftedFiniteForm_hermitian D V)
    (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis (finiteSpectralData D V).finiteEigenvalues
    (finiteSpectralData D V).finiteEigenvalues_pos (finiteSpectralData D V).finiteEigenvalues_antitone
    hb
    (fun u v => finiteH1Jacobi D V u v) (V.C + 1) hs n u hu
  exact h

/-- Finite-sector actual weighted Jacobi index, including empty sectors. -/
lemma finiteCopy_negativeIndex_eq_finite_count :
    KsIndex.NegativeDensity.negativeIndex (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) =
      ((finiteSpectralData D V).finiteStrictCount (V.C + 1) 0 : ℕ∞) := by
  exact @negativeIndex_eq_finite_strict_count (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance inferInstance
    (Module.finrank ℂ (WeightedFiniteAmbient D))
    (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re)
    (finiteH1WeightedValue D) (finiteH1WeightedValue_spec D).1
    (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis
    ((finiteSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).finiteReciprocalShift_monotone (V.C + 1))
    (fun W _ => @trial_dimension_le_ambient (finiteH1Domain D) (WeightedFiniteAmbient D)
      inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D)) inferInstance inferInstance inferInstance
      (finiteH1WeightedValue D) (finiteH1WeightedValue_spec D).1 W)
    (finiteCopyJacobi_finite_spectral_tail D V) (finiteCopyJacobi_finite_minmax D V)

end KsIndex.Spectral
