module

public import KsIndexLean.FiniteFormMinMax
public import KsIndexLean.InfiniteSolutionOrdering
public import KsIndexLean.FiniteSolutionSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
local instance diskJacobiMinMaxInner1 : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

/-- Actual weighted disk Jacobi min-max, for an infinite spectral sector. -/
lemma diskJacobi_infinite_minmax [Infinite (diskSpectralData D V).eigenbasisIndex]
    (n : ℕ) (L : ℝ) :
    (diskSpectralData D V).infiniteReciprocalShift (V.C + 1) n ≤ L ↔
      ∃ W : Submodule ℂ D, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n + 1 ∧
        ∀ u : W, (weakJacobi V (u : D) (u : D)).re ≤
          L * ‖weightedDiskAmbientEmbedding D (u : D)‖ ^ 2 := by
  have hs (u v : D) : shiftedDiskForm D V u v = weakJacobi V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedDiskForm_apply D V u v
  have h := @infinite_unshifted_form_minmax_iff D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (weightedDiskAmbientEmbedding_spec D).1 (shiftedDiskForm_hermitian D V)
    (diskSpectralData D V).infiniteEigenbasis (diskSpectralData D V).infiniteEigenvalues
    (diskSpectralData D V).infiniteEigenvalues_pos (diskSpectralData D V).infiniteEigenvalues_antitone
    (diskSpectralData D V).infiniteEigenbasis_equation
    (fun u v => weakJacobi V u v) (V.C + 1) hs n L
  exact h

/-- Finite disk sectors use a list of the actual complex ambient dimension. -/
lemma diskJacobi_finite_minmax [FiniteDimensional ℂ (WeightedDiskAmbient D)]
    (n : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) (L : ℝ) :
    (diskSpectralData D V).finiteReciprocalShift (V.C + 1) n ≤ L ↔
      ∃ W : Submodule ℂ D, FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n.val + 1 ∧
        ∀ u : W, (weakJacobi V (u : D) (u : D)).re ≤
          L * ‖weightedDiskAmbientEmbedding D (u : D)‖ ^ 2 := by
  have hs (u v : D) : shiftedDiskForm D V u v = weakJacobi V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedDiskForm_apply D V u v
  have hb (i : Fin (Module.finrank ℂ (WeightedDiskAmbient D))) :
      (diskSpectralData D V).operator ((diskSpectralData D V).finiteEigenbasis.toHilbertBasis i) =
        ((diskSpectralData D V).finiteEigenvalues i : ℂ) •
          (diskSpectralData D V).finiteEigenbasis.toHilbertBasis i := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using (diskSpectralData D V).finiteEigenbasis_equation i
  have h := @finite_unshifted_form_minmax_iff D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance (Module.finrank ℂ (WeightedDiskAmbient D))
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (weightedDiskAmbientEmbedding_spec D).1 (shiftedDiskForm_hermitian D V)
    (diskSpectralData D V).finiteEigenbasis.toHilbertBasis (diskSpectralData D V).finiteEigenvalues
    (diskSpectralData D V).finiteEigenvalues_pos (diskSpectralData D V).finiteEigenvalues_antitone hb
    (fun u v => weakJacobi V u v) (V.C + 1) hs n L
  exact h

end KsIndex.Spectral
