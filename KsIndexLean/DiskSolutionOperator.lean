module

public import KsIndexLean.DiskJacobiSesquilinear

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable (D : Submodule ℂ ComplexH1) [CompleteSpace D]

local instance : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

/-- Actual shifted Jacobi solution operator on the weighted ambient disk sector. -/
def diskSolutionOperator (V : BoundedRealPotential) :
    WeightedDiskAmbient D →L[ℂ] WeightedDiskAmbient D := by
  exact compactFormSolution (E := D) (H := WeightedDiskAmbient D)
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)

lemma diskSolutionOperator_compact (V : BoundedRealPotential) :
    IsCompactOperator (diskSolutionOperator D V) := by
  have h := @compactFormSolution_compact D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (weightedDiskAmbientEmbedding_spec D).2.2
  exact h

lemma diskSolutionOperator_selfAdjoint (V : BoundedRealPotential) :
    IsSelfAdjoint (diskSolutionOperator D V) := by
  have h := @compactFormSolution_selfAdjoint D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (shiftedDiskForm_hermitian D V)
  exact h

lemma diskSolutionOperator_nonneg (V : BoundedRealPotential) (f : WeightedDiskAmbient D) :
    0 ≤ (inner ℂ f (diskSolutionOperator D V f)).re := by
  have h := @compactFormSolution_nonneg D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D) f
  exact h

end KsIndex.Spectral
