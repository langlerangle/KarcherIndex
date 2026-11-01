module

public import KsIndexLean.FiniteMinMaxCount
public import KsIndexLean.FiniteCopyJacobiMinMax
public import KsIndexLean.FiniteZeroMultiplicity

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
  [FiniteDimensional ℂ (WeightedFiniteAmbient D)]
local instance finiteCopyFiniteNonpositiveInner : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

lemma finiteCopy_finite_nonpositive_dimension_le (W : Submodule ℂ (finiteH1Domain D)) [FiniteDimensional ℂ W]
    (hW : ∀ u : W, (finiteH1Jacobi D V (u : finiteH1Domain D) (u : finiteH1Domain D)).re ≤ 0) :
    Module.finrank ℂ W ≤ (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 := by
  apply @finite_nonpositive_trial_dimension_le_count (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D)) inferInstance inferInstance
    (Module.finrank ℂ (WeightedFiniteAmbient D))
    (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) (finiteH1WeightedValue D)
    ((finiteSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).finiteReciprocalShift_monotone (V.C + 1))
    (fun W _ => @trial_dimension_le_ambient (finiteH1Domain D) (WeightedFiniteAmbient D)
      inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D)) inferInstance inferInstance
      inferInstance (finiteH1WeightedValue D)
      (finiteH1WeightedValue_spec D).1 W)
    (finiteCopyJacobi_finite_minmax D V) W inferInstance hW

lemma finiteCopy_finite_nonpositive_dimension_attained :
    ∃ W : Submodule ℂ (finiteH1Domain D), FiniteDimensional ℂ W ∧
      Module.finrank ℂ W = (finiteSpectralData D V).finiteWeakCount (V.C + 1) 0 ∧
      ∀ u : W, (finiteH1Jacobi D V (u : finiteH1Domain D) (u : finiteH1Domain D)).re ≤ 0 := by
  apply @exists_finite_nonpositive_trial_of_count (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (SubmoduleClass.toNormedSpace (finiteH1Domain D)) inferInstance inferInstance
    (Module.finrank ℂ (WeightedFiniteAmbient D))
    (fun u : finiteH1Domain D => (finiteH1Jacobi D V u u).re) _ (finiteH1WeightedValue D)
    ((finiteSpectralData D V).finiteReciprocalShift (V.C + 1))
    ((finiteSpectralData D V).finiteReciprocalShift_monotone (V.C + 1))
    (finiteCopyJacobi_finite_minmax D V)
  rw [← finiteJacobiForm_apply]
  exact congrArg (fun f : finiteH1Domain D →L[ℂ] ℂ => (f 0).re) ((finiteJacobiForm D V).toLinearMap.map_zero)

end KsIndex.Spectral
