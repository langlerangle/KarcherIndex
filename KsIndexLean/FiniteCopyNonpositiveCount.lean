module

public import KsIndexLean.FiniteCopyJacobiMinMax
public import KsIndexLean.MinMaxNonpositiveCount

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
  [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
  [Infinite (finiteSpectralData D V).eigenbasisIndex]
local instance finiteCopyNonpositiveCountInner1 : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

/-- Number of nonpositive weighted finite-copy Jacobi eigenvalues, with complex multiplicity. -/
def finiteCopyNonpositiveCount : ℕ :=
  weakSpectralCount ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1)) 0

lemma finiteCopy_nonpositive_dimension_le (W : Submodule ℂ (finiteH1Domain D)) [FiniteDimensional ℂ W]
    (hW : ∀ u : W, (finiteH1Jacobi D V (u : finiteH1Domain D) (u : finiteH1Domain D)).re ≤ 0) :
    Module.finrank ℂ W ≤ finiteCopyNonpositiveCount D V := by
  exact @nonpositive_trial_dimension_le_count (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D)) inferInstance inferInstance (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re)
    (finiteH1WeightedValue D) ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1))
    (finiteCopyJacobi_infinite_minmax D V) W inferInstance hW

lemma finiteCopy_nonpositive_count_attained :
    ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = finiteCopyNonpositiveCount D V ∧
      ∀ u : W, (finiteH1Jacobi D V (u : finiteH1Domain D) (u : finiteH1Domain D)).re ≤ 0 := by
  have hz : (finiteH1Jacobi D V (0 : finiteH1Domain D) (0 : finiteH1Domain D)).re = 0 := by
    rw [← finiteJacobiForm_apply]
    exact congrArg (fun f : finiteH1Domain D →L[ℂ] ℂ => (f 0).re) ((finiteJacobiForm D V).toLinearMap.map_zero)
  exact @exists_nonpositive_trial_of_count (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D)) inferInstance inferInstance (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) hz
    (finiteH1WeightedValue D) ((finiteSpectralData D V).infiniteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_tendsto_atTop (V.C + 1))
    ((finiteSpectralData D V).infiniteReciprocalShift_monotone (V.C + 1))
    (finiteCopyJacobi_infinite_minmax D V)

end KsIndex.Spectral
