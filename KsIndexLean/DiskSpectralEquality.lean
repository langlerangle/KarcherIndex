module

public import KsIndexLean.OrderedSpectralEquality
public import KsIndexLean.DiskNegativeIndex
public import KsIndexLean.DiskFiniteNegativeIndex

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical
variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
local instance diskSpectralEqualityInner : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

lemma diskJacobi_infinite_tail_equality [Infinite (diskSpectralData D V).eigenbasisIndex]
    (n : ℕ) (u : D)
    (hu : ∀ i < n, inner ℂ ((diskSpectralData D V).infiniteEigenbasis i)
      (weightedDiskAmbientEmbedding D u) = 0)
    (heq : (weakJacobi V u u).re = (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n *
      ‖weightedDiskAmbientEmbedding D u‖ ^ 2) :
    ∀ w : D, weakJacobi V u w =
      ((diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w) := by
  have hs (x y : D) : shiftedDiskForm D V x y = domainJacobiForm D V x y +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D x) (weightedDiskAmbientEmbedding D y) := by
    simpa only [domainJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
      shiftedDiskForm_apply D V x y
  exact @ordered_spectral_tail_equality D (WeightedDiskAmbient D) ℕ
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (domainJacobiForm D V) (shiftedDiskForm_coercive D V)
    (weightedDiskAmbientEmbedding D) (shiftedDiskForm_hermitian D V)
    (fun x y => weakJacobi_conj V x y)
    (diskSpectralData D V).infiniteEigenbasis (diskSpectralData D V).infiniteEigenvalues
    (diskSpectralData D V).infiniteEigenvalues_pos (diskSpectralData D V).infiniteEigenvalues_antitone
    (diskSpectralData D V).infiniteEigenbasis_equation (V.C + 1) hs n (Finset.range n)
    (fun i => Finset.mem_range) u hu heq

lemma diskJacobi_finite_tail_equality [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) (u : D)
    (hu : ∀ i < n, inner ℂ ((diskSpectralData D V).finiteEigenbasis.toHilbertBasis i)
      (weightedDiskAmbientEmbedding D u) = 0)
    (heq : (weakJacobi V u u).re = (diskSpectralData D V).finiteReciprocalShift (V.C + 1) n *
      ‖weightedDiskAmbientEmbedding D u‖ ^ 2) :
    ∀ w : D, weakJacobi V u w =
      ((diskSpectralData D V).finiteReciprocalShift (V.C + 1) n : ℂ) *
        inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D w) := by
  have hs (x y : D) : shiftedDiskForm D V x y = domainJacobiForm D V x y +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D x) (weightedDiskAmbientEmbedding D y) := by
    simpa only [domainJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
      shiftedDiskForm_apply D V x y
  have hb (i : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) :
      (diskSpectralData D V).operator ((diskSpectralData D V).finiteEigenbasis.toHilbertBasis i) =
        ((diskSpectralData D V).finiteEigenvalues i : ℂ) •
          (diskSpectralData D V).finiteEigenbasis.toHilbertBasis i := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using (diskSpectralData D V).finiteEigenbasis_equation i
  exact @ordered_spectral_tail_equality D (WeightedDiskAmbient D) (Fin (Module.finrank ℂ (WeightedDiskAmbient D)))
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (domainJacobiForm D V) (shiftedDiskForm_coercive D V)
    (weightedDiskAmbientEmbedding D) (shiftedDiskForm_hermitian D V)
    (fun x y => weakJacobi_conj V x y)
    (diskSpectralData D V).finiteEigenbasis.toHilbertBasis (diskSpectralData D V).finiteEigenvalues
    (diskSpectralData D V).finiteEigenvalues_pos (diskSpectralData D V).finiteEigenvalues_antitone
    hb (V.C + 1) hs n (Finset.Iio n)
    (fun i => Finset.mem_Iio) u hu heq

end KsIndex.Spectral
