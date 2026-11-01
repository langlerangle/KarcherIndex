module

public import KsIndexLean.ComplexCoerciveOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section


noncomputable section
namespace KsIndex.Spectral

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Variational solution in the form domain, over the complex scalar field. -/
def formSolution (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) : H →L[ℂ] E :=
  (coerciveFormEquiv B hB).symm.toContinuousLinearMap.comp J.adjoint

lemma formSolution_weak (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (f : H) (v : E) :
    B (formSolution B hB J f) v = inner ℂ f (J v) := by
  rw [formSolution, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    coerciveFormEquiv_weak, ContinuousLinearMap.adjoint_inner_left]

/-- Solution operator acting on the ambient mass Hilbert space.
It is compact when `J` is compact, as proved by `compactFormSolution_compact`. -/
def compactFormSolution (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) : H →L[ℂ] H :=
  J.comp (formSolution B hB J)

lemma compactFormSolution_compact (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (hJ : IsCompactOperator J) :
    IsCompactOperator (compactFormSolution B hB J) := hJ.comp_clm (formSolution B hB J)

lemma compactFormSolution_symmetric (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hherm : ∀ u v, star (B v u) = B u v) :
    (compactFormSolution B hB J).toLinearMap.IsSymmetric := by
  intro f g
  have hf := formSolution_weak B hB J f (formSolution B hB J g)
  have hg := formSolution_weak B hB J g (formSolution B hB J f)
  have hc := hherm (formSolution B hB J f) (formSolution B hB J g)
  rw [hg, hf] at hc
  change (starRingEnd ℂ) (inner ℂ g (J (formSolution B hB J f))) = _ at hc
  rw [inner_conj_symm] at hc
  exact hc

lemma compactFormSolution_selfAdjoint (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H)
    (hherm : ∀ u v, star (B v u) = B u v) :
    IsSelfAdjoint (compactFormSolution B hB J) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (compactFormSolution_symmetric B hB J hherm)

lemma compactFormSolution_nonneg (B : E →L⋆[ℂ] E →L[ℂ] ℂ)
    (hB : ∀ u, ‖u‖ ^ 2 ≤ (B u u).re) (J : E →L[ℂ] H) (f : H) :
    0 ≤ (inner ℂ f (compactFormSolution B hB J f)).re := by
  have he := formSolution_weak B hB J f (formSolution B hB J f)
  have hc := hB (formSolution B hB J f)
  rw [he] at hc
  exact (sq_nonneg _).trans hc

end KsIndex.Spectral
