module

public import KsIndexLean.FiniteJacobiSesquilinear

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
  [CompleteSpace (finiteH1Domain D)]

local instance : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

/-- Actual shifted Jacobi solution operator on the weighted ambient finite-copy sector. -/
def finiteSolutionOperator (V : BoundedRealPotential) :
    WeightedFiniteAmbient D →L[ℂ] WeightedFiniteAmbient D := by
  exact compactFormSolution (E := finiteH1Domain D) (H := WeightedFiniteAmbient D)
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)

lemma finiteSolutionOperator_compact (V : BoundedRealPotential) :
    IsCompactOperator (finiteSolutionOperator D V) := by
  have h := @compactFormSolution_compact (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (finiteH1WeightedValue_spec D).2.2
  exact h

lemma finiteSolutionOperator_selfAdjoint (V : BoundedRealPotential) :
    IsSelfAdjoint (finiteSolutionOperator D V) := by
  have h := @compactFormSolution_selfAdjoint (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (shiftedFiniteForm_hermitian D V)
  exact h

lemma finiteSolutionOperator_nonneg (V : BoundedRealPotential) (f : WeightedFiniteAmbient D) :
    0 ≤ (inner ℂ f (finiteSolutionOperator D V f)).re := by
  have h := @compactFormSolution_nonneg (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D) f
  exact h

lemma finiteSolutionOperator_injective {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) : Function.Injective (finiteSolutionOperator D V) := by
  have h := @compactFormSolution_injective (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (finiteH1WeightedValue_spec D).1 (finiteH1WeightedValue_spec D).2.1
  exact h

lemma finiteSolutionOperator_strictPositive {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) {f : WeightedFiniteAmbient D} (hf : f ≠ 0) :
    0 < (inner ℂ f (finiteSolutionOperator D V f)).re := by
  have h := @compactFormSolution_strictPositive (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (finiteH1WeightedValue_spec D).2.1 f hf
  exact h

lemma finiteSolutionOperator_denseRange {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) : DenseRange (finiteSolutionOperator D V) :=
  selfAdjoint_injective_denseRange _ (finiteSolutionOperator_selfAdjoint D V)
    (finiteSolutionOperator_injective D V)


end KsIndex.Spectral
