module

public import KsIndexLean.WeakLocalizedEquation
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! Explicit conversion from the sesquilinear form convention (conjugated
field slot) to the bilinear interior weak PDE. The potential is real. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped Distributions
namespace KsIndex.Weq

/-- Conjugating the test and then the identity removes the field conjugation.
No sign or phase is silently absorbed in this conversion. -/
theorem interiorWeakEquation_of_sesquilinear {Ω : Opens ℂ}
    {u ux uy : ℂ → ℂ} {V : ℂ → ℝ}
    (h : ∀ ψ : 𝓓(Ω, ℂ),
      (∫ z, starRingEnd ℂ (ux z) * fderiv ℝ (ψ : ℂ → ℂ) z 1 +
        starRingEnd ℂ (uy z) * fderiv ℝ (ψ : ℂ → ℂ) z Complex.I) =
      ∫ z, (V z : ℂ) * starRingEnd ℂ (u z) * ψ z) :
    InteriorWeakEquation Ω ux uy (fun z => (V z : ℂ) * u z) := by
  intro ψ
  let ψc : 𝓓(Ω, ℂ) := TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap ψ
  have hd (z d : ℂ) : fderiv ℝ (ψc : ℂ → ℂ) z d =
      starRingEnd ℂ (fderiv ℝ (ψ : ℂ → ℂ) z d) := by
    exact congrArg (fun L : ℂ →L[ℝ] ℂ => L d)
      (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z
        (ψ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
  have he := congrArg (starRingEnd ℂ) (h ψc)
  rw [← integral_conj, ← integral_conj] at he
  simp_rw [hd, map_add, map_mul, starRingEnd_self_apply] at he
  have htest (z : ℂ) : starRingEnd ℂ (ψc z) = ψ z := by
    change starRingEnd ℂ (starRingEnd ℂ (ψ z)) = ψ z
    simp
  simp_rw [htest, Complex.conj_ofReal] at he
  convert he using 1 <;> congr 1 <;> funext z <;> ring

end KsIndex.Weq
