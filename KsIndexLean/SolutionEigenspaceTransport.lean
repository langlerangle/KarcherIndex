module

public import KsIndexLean.WeakSolutionEigenvalue
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Module.End

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Form-domain realization of an ambient solution eigenspace. -/
def solutionFormEigenspace (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (t : ℂ) : Submodule ℂ E :=
  (eigenspace (compactFormSolution B hB J).toLinearMap t).comap J.toLinearMap

lemma mem_solutionFormEigenspace_iff (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (t : ℝ) (ht : t ≠ 0) (u : E) :
    u ∈ solutionFormEigenspace B hB J (t : ℂ) ↔
      ∀ v, B u v = (t⁻¹ : ℝ) * inner ℂ (J u) (J v) := by
  change J u ∈ eigenspace (compactFormSolution B hB J).toLinearMap (t : ℂ) ↔ _
  rw [mem_eigenspace_iff]
  exact compactFormSolution_real_eigen_iff B hB J hJ u t ht

/-- The embedding identifies the two eigenspaces over C. Surjectivity follows
from the nonzero-eigenvalue regularity lemma, not an extra regularity axiom. -/
def solutionEigenspaceEquiv (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (t : ℂ) (ht : t ≠ 0) :
    solutionFormEigenspace B hB J t ≃ₗ[ℂ]
      eigenspace (compactFormSolution B hB J).toLinearMap t := by
  let F : solutionFormEigenspace B hB J t →ₗ[ℂ]
      eigenspace (compactFormSolution B hB J).toLinearMap t :=
    { toFun := fun u => ⟨J u, u.property⟩
      map_add' := fun u v => Subtype.ext (map_add J (u : E) (v : E))
      map_smul' := fun a u => Subtype.ext (map_smul J a (u : E)) }
  apply LinearEquiv.ofBijective F
  constructor
  · intro u v h
    exact Subtype.ext (hJ (congrArg Subtype.val h))
  · intro f
    obtain ⟨u, hu⟩ := compactFormSolution_eigen_mem_range B hB J ht
      (mem_eigenspace_iff.mp f.property)
    refine ⟨⟨u, ?_⟩, ?_⟩
    · change J u ∈ eigenspace (compactFormSolution B hB J).toLinearMap t
      rw [show J u = f.val from hu]
      exact f.property
    · exact Subtype.ext hu

/-- Complex multiplicity is unchanged on passage to weak form eigenvectors. -/
lemma solutionFormEigenspace_finrank (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (t : ℂ) (ht : t ≠ 0) :
    Module.finrank ℂ (solutionFormEigenspace B hB J t) =
      Module.finrank ℂ (eigenspace (compactFormSolution B hB J).toLinearMap t) :=
  (solutionEigenspaceEquiv B hB J hJ t ht).finrank_eq

/-- Compactness makes each nonzero weak eigenspace finite dimensional. -/
lemma solutionFormEigenspace_finiteDimensional (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hJ : Function.Injective J) (hcompact : IsCompactOperator J)
    (t : ℂ) (ht : t ≠ 0) :
    FiniteDimensional ℂ (solutionFormEigenspace B hB J t) := by
  let := ContinuousLinearMap.finite_dimensional_eigenspace
    (compactFormSolution_compact B hB J hcompact) t ht
  exact (solutionEigenspaceEquiv B hB J hJ t ht).symm.finiteDimensional

end KsIndex.Spectral
