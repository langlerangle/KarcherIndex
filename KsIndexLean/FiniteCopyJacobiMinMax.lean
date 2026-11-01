module

public import KsIndexLean.FiniteFormMinMax
public import KsIndexLean.InfiniteSolutionOrdering
public import KsIndexLean.FiniteSolutionSpectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
  [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
local instance finiteCopyJacobiMinMaxInner1 : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

/-- Actual weighted finite-copy Jacobi min-max, for an infinite spectral sector. -/
lemma finiteCopyJacobi_infinite_minmax [Infinite (finiteSpectralData D V).eigenbasisIndex]
    (n : ℕ) (L : ℝ) :
    (finiteSpectralData D V).infiniteReciprocalShift (V.C + 1) n ≤ L ↔
      ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n + 1 ∧
        ∀ u : W, (finiteH1Jacobi D V (u : finiteH1Domain D) (u : finiteH1Domain D)).re ≤
          L * ‖finiteH1WeightedValue D (u : finiteH1Domain D)‖ ^ 2 := by
  have hs (u v : finiteH1Domain D) : shiftedFiniteForm D V u v = finiteH1Jacobi D V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedFiniteForm_apply D V u v
  have h := @infinite_unshifted_form_minmax_iff (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (finiteH1WeightedValue_spec D).1 (shiftedFiniteForm_hermitian D V)
    (finiteSpectralData D V).infiniteEigenbasis (finiteSpectralData D V).infiniteEigenvalues
    (finiteSpectralData D V).infiniteEigenvalues_pos (finiteSpectralData D V).infiniteEigenvalues_antitone
    (finiteSpectralData D V).infiniteEigenbasis_equation
    (fun u v => finiteH1Jacobi D V u v) (V.C + 1) hs n L
  exact h

/-- Finite-dimensional finite-copy sectors use a list of the actual complex ambient dimension. -/
lemma finiteCopyJacobi_finite_minmax [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
    (n : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) (L : ℝ) :
    (finiteSpectralData D V).finiteReciprocalShift (V.C + 1) n ≤ L ↔
      ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧ Module.finrank ℂ W = n.val + 1 ∧
        ∀ u : W, (finiteH1Jacobi D V (u : finiteH1Domain D) (u : finiteH1Domain D)).re ≤
          L * ‖finiteH1WeightedValue D (u : finiteH1Domain D)‖ ^ 2 := by
  have hs (u v : finiteH1Domain D) : shiftedFiniteForm D V u v = finiteH1Jacobi D V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedFiniteForm_apply D V u v
  have hb (i : Fin (Module.finrank ℂ (WeightedFiniteAmbient D))) :
      (finiteSpectralData D V).operator ((finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i) =
        ((finiteSpectralData D V).finiteEigenvalues i : ℂ) •
          (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis i := by
    simpa only [OrthonormalBasis.coe_toHilbertBasis] using (finiteSpectralData D V).finiteEigenbasis_equation i
  have h := @finite_unshifted_form_minmax_iff (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance (Module.finrank ℂ (WeightedFiniteAmbient D))
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (finiteH1WeightedValue_spec D).1 (shiftedFiniteForm_hermitian D V)
    (finiteSpectralData D V).finiteEigenbasis.toHilbertBasis (finiteSpectralData D V).finiteEigenvalues
    (finiteSpectralData D V).finiteEigenvalues_pos (finiteSpectralData D V).finiteEigenvalues_antitone hb
    (fun u v => finiteH1Jacobi D V u v) (V.C + 1) hs n L
  exact h

end KsIndex.Spectral
