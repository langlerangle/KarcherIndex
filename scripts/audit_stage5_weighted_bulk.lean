module

public import KsIndexLean.SphericalBulkMap

@[expose] public section

noncomputable section
open KsIndex.WeakH1 KsIndex.Spherical
example (D : Submodule ℂ ComplexH1) : InnerProductSpace ℂ (WeightedDiskAmbient D) := inferInstance
example (D : Submodule ℂ ComplexH1) : CompleteSpace (WeightedDiskAmbient D) := inferInstance
#print axioms sphericalBulkCLM
#print axioms weightedDiskValueCLM_compact
#print axioms weightedDiskAmbientEmbedding_spec
#print axioms weightedDiskAmbient_shift_coercive
