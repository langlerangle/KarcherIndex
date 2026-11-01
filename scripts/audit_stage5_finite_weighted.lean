module

public import KsIndexLean.FiniteHilbertFormDomain

@[expose] public section

noncomputable section
open KsIndex.WeakH1 KsIndex.Spherical KsIndex.Spectral
example {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    InnerProductSpace ℂ (finiteH1Domain D) := inferInstance
example {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    InnerProductSpace ℂ (WeightedFiniteAmbient D) := inferInstance
example {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    CompleteSpace (WeightedFiniteAmbient D) := inferInstance
#print axioms weightedFiniteAmbientEmbedding_spec
#print axioms weightedFiniteAmbient_shift_coercive
#print axioms finiteH1DomainCoordinates_bijective
#print axioms finiteH1WeightedValue_spec
#print axioms finiteH1Weighted_shift_coercive
#print axioms finiteH1Domain_completeSpace
