module

public import KsIndexLean.FiniteSolutionOperator
public import KsIndexLean.WeakSolutionEigenvalue

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open KsIndex.WeakH1 KsIndex.Spherical

section Disk
variable (D : Submodule ℂ ComplexH1) [CompleteSpace D]
local instance jacobiSolutionEigenvalueInner1 : InnerProductSpace ℂ D := diskDomain_innerProductSpace D

/-- The concrete disk solution spectrum is the reciprocal shifted weak Jacobi
spectrum, with the actual weighted bulk mass and the original form domain. -/
lemma diskSolutionOperator_eigen_iff
    (V : BoundedRealPotential) (u : D) (t : ℝ) (ht : t ≠ 0) :
    diskSolutionOperator D V (weightedDiskAmbientEmbedding D u) =
        (t : ℂ) • weightedDiskAmbientEmbedding D u ↔
      ∀ v : D, weakJacobi V u v = ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) *
        inner ℂ (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
  have hs (u v : D) : shiftedDiskForm D V u v = weakJacobi V u v +
      ((V.C + 1 : ℝ) : ℂ) * inner ℂ
        (weightedDiskAmbientEmbedding D u) (weightedDiskAmbientEmbedding D v) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_one] using shiftedDiskForm_apply D V u v
  have h := @compactFormSolution_shifted_eigen_iff D (WeightedDiskAmbient D)
    inferInstance (diskDomain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedDiskForm D V) (shiftedDiskForm_coercive D V) (weightedDiskAmbientEmbedding D)
    (weightedDiskAmbientEmbedding_spec D).1 (fun u v => weakJacobi V u v) (V.C + 1)
    hs u t ht
  exact h

end Disk

/-- The same exact weak-equation identification on ordered finite-copy domains. -/
lemma finiteSolutionOperator_eigen_iff {ι : Type*} [Fintype ι]
    (D : Submodule ℂ (ι → ComplexH1)) [CompleteSpace (finiteH1Domain D)]
    (V : BoundedRealPotential) (u : finiteH1Domain D) (t : ℝ) (ht : t ≠ 0) :
    finiteSolutionOperator D V (finiteH1WeightedValue D u) =
        (t : ℂ) • finiteH1WeightedValue D u ↔
      ∀ v : finiteH1Domain D, finiteH1Jacobi D V u v = ((t⁻¹ - (V.C + 1) : ℝ) : ℂ) *
        inner ℂ (finiteH1WeightedValue D u) (finiteH1WeightedValue D v) := by
  have h := @compactFormSolution_shifted_eigen_iff (finiteH1Domain D) (WeightedFiniteAmbient D)
    inferInstance (finiteH1Domain_innerProductSpace D) inferInstance
    inferInstance inferInstance inferInstance
    (shiftedFiniteForm D V) (shiftedFiniteForm_coercive D V) (finiteH1WeightedValue D)
    (finiteH1WeightedValue_spec D).1 (finiteH1Jacobi D V) (V.C + 1)
    (fun u v => by simpa only [Complex.ofReal_add, Complex.ofReal_one] using
      shiftedFiniteForm_apply D V u v) u t ht
  exact h

end KsIndex.Spectral
