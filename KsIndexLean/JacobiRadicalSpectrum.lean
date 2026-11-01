module

public import KsIndexLean.SolutionEigenspaceTransport

@[expose] public section


noncomputable section
namespace KsIndex.Spectral
open Module.End

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weak radical: vectors whose pairing with every form-domain vector vanishes. -/
def formRadical (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) : Submodule ℂ E := Q.toLinearMap.ker

omit [CompleteSpace E] in
lemma mem_formRadical (Q : E →L⋆[ℂ] E →L[ℂ] ℂ) (u : E) :
    u ∈ formRadical Q ↔ ∀ v, Q u v = 0 := by
  change Q u = 0 ↔ _
  constructor
  · intro h v
    rw [h, zero_apply]
  · intro h
    ext v
    exact h v

/-- The zero weak-Jacobi eigenspace corresponds to solution eigenvalue `1/c`. -/
lemma formRadical_eq_solutionEigenspace (B Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hJ : Function.Injective J)
    (c : ℝ) (hc : c ≠ 0)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v)) :
    formRadical Q = solutionFormEigenspace B hB J ((c⁻¹ : ℝ) : ℂ) := by
  ext u
  rw [mem_formRadical, mem_solutionFormEigenspace_iff B hB J hJ (c⁻¹) (inv_ne_zero hc)]
  simp only [inv_inv]
  constructor
  · intro h v
    rw [hshift, h v, zero_add]
  · intro h v
    have hv := h v
    rw [hshift] at hv
    exact add_eq_right.mp hv

/-- Complex-linear radical/eigenspace identification; no smoothness hypothesis. -/
def formRadicalEquiv (B Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hJ : Function.Injective J)
    (c : ℝ) (hc : c ≠ 0)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v)) :
    formRadical Q ≃ₗ[ℂ] eigenspace (compactFormSolution B hB J).toLinearMap ((c⁻¹ : ℝ) : ℂ) :=
  (LinearEquiv.ofEq _ _ (formRadical_eq_solutionEigenspace B Q hB J hJ c hc hshift)).trans
    (solutionEigenspaceEquiv B hB J hJ _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hc)))

lemma formRadical_finiteDimensional (B Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hJ : Function.Injective J)
    (hcompact : IsCompactOperator J) (c : ℝ) (hc : c ≠ 0)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v)) :
    FiniteDimensional ℂ (formRadical Q) := by
  let := ContinuousLinearMap.finite_dimensional_eigenspace
    (compactFormSolution_compact B hB J hcompact) ((c⁻¹ : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero hc))
  exact (formRadicalEquiv B Q hB J hJ c hc hshift).symm.finiteDimensional

lemma formRadical_finrank_eq_eigenspace (B Q : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hJ : Function.Injective J)
    (c : ℝ) (hc : c ≠ 0)
    (hshift : ∀ u v, B u v = Q u v + (c : ℂ) * inner ℂ (J u) (J v)) :
    Module.finrank ℂ (formRadical Q) =
      Module.finrank ℂ (eigenspace (compactFormSolution B hB J).toLinearMap ((c⁻¹ : ℝ) : ℂ)) :=
  (formRadicalEquiv B Q hB J hJ c hc hshift).finrank_eq

end KsIndex.Spectral
