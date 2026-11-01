module

public import KsIndexLean.OrderedSpectralEquality
public import KsIndexLean.FiniteCopyNegativeIndex
public import KsIndexLean.FiniteCopyFiniteNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical
variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
local instance finiteCopySpectralEqualityInner : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

lemma finiteCopyJacobi_infinite_tail_equality [Infinite (finiteSpectralData D V).eigenbasisIndex]
    (n : ℕ) (u : finiteH1Domain D)
    (hu : ∀ i < n, inner ℂ ((finiteSpectralData D V).infiniteEigenbasis i)
      (finiteH1WeightedValue D u) = 0)
    (heq : (finiteH1Jacobi D V u u).re = (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n *
      ‖finiteH1WeightedValue D u‖ ^ 2) :
    ∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
      ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w) := by
  have hs (x y : finiteH1Domain D) : shiftedFiniteForm D V x y = finiteJacobiForm D V x y +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (finiteH1WeightedValue D x) (finiteH1WeightedValue D y) := by
    simpa only [finiteJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
      shiftedFiniteForm_apply D V x y
  have h := @ordered_spectral_tail_equality (finiteH1Domain D) (WeightedFiniteAmbient D) ℕ
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (finiteJacobiForm D V) (shiftedFiniteForm_coercive D V)
    (finiteH1WeightedValue D) (shiftedFiniteForm_hermitian D V)
    (finiteJacobiForm_hermitian D V)
    (finiteSpectralData D V).infiniteEigenbasis (finiteSpectralData D V).infiniteEigenvalues
    (finiteSpectralData D V).infiniteEigenvalues_pos (finiteSpectralData D V).infiniteEigenvalues_antitone
    (finiteSpectralData D V).infiniteEigenbasis_equation (V.C + 1) hs n (Finset.range n)
    (fun i => Finset.mem_range) u hu (by simpa only [finiteJacobiForm_apply, PositiveCompactSolution.infiniteReciprocalShift, PositiveCompactSolution.finiteReciprocalShift] using heq)
  simpa only [finiteJacobiForm_apply, PositiveCompactSolution.infiniteReciprocalShift, PositiveCompactSolution.finiteReciprocalShift] using h

lemma finiteCopyJacobi_finite_tail_equality [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) (u : finiteH1Domain D)
    (hu : ∀ i < n, inner ℂ ((finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i)
      (finiteH1WeightedValue D u) = 0)
    (heq : (finiteH1Jacobi D V u u).re = (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) n *
      ‖finiteH1WeightedValue D u‖ ^ 2) :
    ∀ w : finiteH1Domain D, finiteH1Jacobi D V u w =
      ((finiteSpectralData D V).finiteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D w) := by
  have hs (x y : finiteH1Domain D) : shiftedFiniteForm D V x y = finiteJacobiForm D V x y +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (finiteH1WeightedValue D x) (finiteH1WeightedValue D y) := by
    simpa only [finiteJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
      shiftedFiniteForm_apply D V x y
  have hb (i : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) :
      (finiteSpectralData D V).operator ((finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i) =
        ((finiteSpectralData D V).finiteEigenvalues i : ℂ) •
          (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using (finiteSpectralData D V).finiteEigenbasis_equation i
  have h := @ordered_spectral_tail_equality (finiteH1Domain D) (WeightedFiniteAmbient D) (Fin (Module.finrank ℂ (WeightedFiniteAmbient D)))
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (finiteJacobiForm D V) (shiftedFiniteForm_coercive D V)
    (finiteH1WeightedValue D) (shiftedFiniteForm_hermitian D V)
    (finiteJacobiForm_hermitian D V)
    (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis (finiteSpectralData D V).finiteEigenvalues
    (finiteSpectralData D V).finiteEigenvalues_pos (finiteSpectralData D V).finiteEigenvalues_antitone
    hb (V.C + 1) hs n (Finset.Iio n)
    (fun i => Finset.mem_Iio) u hu (by simpa only [finiteJacobiForm_apply, PositiveCompactSolution.infiniteReciprocalShift, PositiveCompactSolution.finiteReciprocalShift] using heq)
  simpa only [finiteJacobiForm_apply, PositiveCompactSolution.infiniteReciprocalShift, PositiveCompactSolution.finiteReciprocalShift] using h

end KsIndex.Spectral
