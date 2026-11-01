module

public import KsIndexLean.JacobiRadicalSpectrum
public import KsIndexLean.FiniteSolutionOperator

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical Module.End

section Disk
variable (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential)
local instance jacobiRadicalRealizationInner1 : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

/-- Actual weak disk radical, identified over C with the reciprocal-shift eigenspace. -/
def diskRadicalEquiv : (@formRadical D inferInstance (diskDomain_innerProductSpace D) (domainJacobiForm D V)) ≃ₗ[ℂ]
    eigenspace (diskSolutionOperator D V).toLinearMap (((V.C + 1)⁻¹ : ℝ) : ℂ) := by
  have hs (u v : D) : shiftedDiskForm D V u v = domainJacobiForm D V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
    simpa only [domainJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
      shiftedDiskForm_apply D V u v
  exact @formRadicalEquiv D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (domainJacobiForm D V) (shiftedDiskForm_coercive D V)
    (weightedDiskAmbientEmbedding D) (weightedDiskAmbientEmbedding_spec D).1
    (V.C + 1) (by linarith [V.nonneg]) hs

lemma diskRadical_finiteDimensional : FiniteDimensional ℂ ((@formRadical D inferInstance (diskDomain_innerProductSpace D) (domainJacobiForm D V))) := by
  let := ContinuousLinearMap.finite_dimensional_eigenspace (diskSolutionOperator_compact D V)
    (((V.C + 1)⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero (by linarith [V.nonneg])))
  exact (diskRadicalEquiv D V).symm.finiteDimensional

lemma diskRadical_finrank : Module.finrank ℂ ((@formRadical D inferInstance (diskDomain_innerProductSpace D) (domainJacobiForm D V))) =
    Module.finrank ℂ (eigenspace (diskSolutionOperator D V).toLinearMap (((V.C + 1)⁻¹ : ℝ) : ℂ)) :=
  (diskRadicalEquiv D V).finrank_eq
end Disk

section FiniteCopy
variable {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
  [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential)
local instance jacobiRadicalRealizationInner2 : InnerProductSpace ℂ (finiteH1Domain D) := finiteH1Domain_innerProductSpace D

def finiteCopyRadicalEquiv : (@formRadical (finiteH1Domain D) inferInstance (finiteH1Domain_innerProductSpace D) (finiteJacobiForm D V)) ≃ₗ[ℂ]
    eigenspace (finiteSolutionOperator D V).toLinearMap (((V.C + 1)⁻¹ : ℝ) : ℂ) := by
  have hs (u v : finiteH1Domain D) : shiftedFiniteForm D V u v = finiteJacobiForm D V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
    simpa only [finiteJacobiForm_apply, Complex.ofReal_add, Complex.ofReal_one] using
      shiftedFiniteForm_apply D V u v
  exact @formRadicalEquiv (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (finiteJacobiForm D V) (shiftedFiniteForm_coercive D V)
    (finiteH1WeightedValue D) (finiteH1WeightedValue_spec D).1
    (V.C + 1) (by linarith [V.nonneg]) hs

lemma finiteCopyRadical_finiteDimensional : FiniteDimensional ℂ ((@formRadical (finiteH1Domain D) inferInstance (finiteH1Domain_innerProductSpace D) (finiteJacobiForm D V))) := by
  let := ContinuousLinearMap.finite_dimensional_eigenspace (finiteSolutionOperator_compact D V)
    (((V.C + 1)⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero (by linarith [V.nonneg])))
  exact (finiteCopyRadicalEquiv D V).symm.finiteDimensional

lemma finiteCopyRadical_finrank : Module.finrank ℂ ((@formRadical (finiteH1Domain D) inferInstance (finiteH1Domain_innerProductSpace D) (finiteJacobiForm D V))) =
    Module.finrank ℂ (eigenspace (finiteSolutionOperator D V).toLinearMap (((V.C + 1)⁻¹ : ℝ) : ℂ)) :=
  (finiteCopyRadicalEquiv D V).finrank_eq
end FiniteCopy
end KsIndex.Spectral
