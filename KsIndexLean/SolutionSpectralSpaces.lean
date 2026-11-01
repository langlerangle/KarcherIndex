module

public import KsIndexLean.FiniteSolutionOperator
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Module.End

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Properties already proved for concrete solution operators, over complex scalars. -/
structure PositiveCompactSolution (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  operator : H →L[ℂ] H
  compact : IsCompactOperator operator
  selfAdjoint : IsSelfAdjoint operator
  injective : Function.Injective operator
  positive : ∀ f, f ≠ 0 → 0 < (inner ℂ f (operator f)).re

namespace PositiveCompactSolution
variable (S : PositiveCompactSolution H)

lemma symmetric : S.operator.toLinearMap.IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.selfAdjoint

lemma zero_eigenspace : eigenspace S.operator.toLinearMap 0 = ⊥ := by
  rw [eigenspace_zero]
  exact LinearMap.ker_eq_bot.mpr S.injective

lemma eigenspaces_complete :
    (⨆ μ : ℂ, eigenspace S.operator.toLinearMap μ).topologicalClosure = ⊤ := by
  have h := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot S.compact S.symmetric
  rw [← Submodule.orthogonal_orthogonal_eq_closure, h, Submodule.bot_orthogonal_eq_top]

lemma eigenspace_finite (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (eigenspace S.operator.toLinearMap μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace S.compact μ hμ

lemma eigenvalue_pos {μ : ℝ} (hμ : HasEigenvalue S.operator.toLinearMap (μ : ℂ)) : 0 < μ :=
  eigenvalue_pos_of_pos hμ S.positive

lemma eigenvalue_real {μ : ℂ} (hμ : HasEigenvalue S.operator.toLinearMap μ) :
    (μ.re : ℂ) = μ := by
  have hc := S.symmetric.conj_eigenvalue_eq_self hμ
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  have hz : μ.im = 0 := by linarith
  apply Complex.ext <;> simp [hz]

lemma eigenvalue_re_pos {μ : ℂ} (hμ : HasEigenvalue S.operator.toLinearMap μ) : 0 < μ.re := by
  have he := S.eigenvalue_real hμ
  apply S.eigenvalue_pos
  rwa [he]

end PositiveCompactSolution

open KsIndex.WeakH1 KsIndex.Spherical

def diskSpectralData (D : Submodule ℂ ComplexH1) [CompleteSpace D] (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedDiskAmbient D) where
  operator := diskSolutionOperator D V
  compact := diskSolutionOperator_compact D V
  selfAdjoint := diskSolutionOperator_selfAdjoint D V
  injective := diskSolutionOperator_injective D V
  positive := fun _ hf => diskSolutionOperator_strictPositive D V hf

def finiteSpectralData {ι : Type*} [Fintype ι] (D : Submodule ℂ (ι → ComplexH1))
    [CompleteSpace (finiteH1Domain D)] (V : BoundedRealPotential) :
    PositiveCompactSolution (WeightedFiniteAmbient D) where
  operator := finiteSolutionOperator D V
  compact := finiteSolutionOperator_compact D V
  selfAdjoint := finiteSolutionOperator_selfAdjoint D V
  injective := finiteSolutionOperator_injective D V
  positive := fun _ hf => finiteSolutionOperator_strictPositive D V hf

end KsIndex.Spectral
