module

public import KsIndexLean.BulkHilbertDomains

@[expose] public section

noncomputable section
open KsIndex.WeakH1 KsIndex.Trace KsIndex.Spectral
example (D : Submodule ℂ ComplexH1) : InnerProductSpace ℂ (DiskAmbient D) := inferInstance
example (D : Submodule ℂ ComplexH1) : CompleteSpace (DiskAmbient D) := inferInstance
example (D : Submodule ℂ DiskPairH1) : InnerProductSpace ℂ (PairAmbient D) := inferInstance
example (D : Submodule ℂ DiskPairH1) : CompleteSpace (PairAmbient D) := inferInstance
example {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    InnerProductSpace ℂ (FiniteAmbient D) := inferInstance
example {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1)) :
    CompleteSpace (FiniteAmbient D) := inferInstance
#print axioms closureEmbedding_denseRange
#print axioms closureEmbedding_compact
#print axioms diskAmbientEmbedding_spec
#print axioms pairAmbientEmbedding_spec
#print axioms finiteAmbientEmbedding_spec
