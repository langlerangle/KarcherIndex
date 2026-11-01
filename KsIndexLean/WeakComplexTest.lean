module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section


/-! Complex-valued test functions for the real-directional weak derivative.
All pairings in this file are bilinear; no complex conjugation is introduced. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped Distributions
namespace KsIndex.WeakComplexTest

lemma lineDeriv_postcomp {f : ℂ → ℂ} {x : ℂ} (hf : DifferentiableAt ℝ f x)
    (T : ℂ →L[ℝ] ℝ) (d : ℂ) :
    lineDeriv ℝ (fun z => T (f z)) x d = T (lineDeriv ℝ f x d) := by
  rw [hf.lineDeriv_eq_fderiv]
  exact ((T.hasFDerivAt.comp x hf.hasFDerivAt).hasLineDerivAt d).lineDeriv

/-- TauCeti's real-test IBP extends to complex tests by real/imaginary decomposition. -/
theorem integral_lineDeriv_mul_eq_neg {Ω : Opens ℂ} {u v : ℂ → ℂ} {d : ℂ}
    (h : TauCeti.HasWeakLineDerivOn volume Ω u v d) (φ : 𝓓(Ω, ℂ)) :
    (∫ z, lineDeriv ℝ (φ : ℂ → ℂ) z d * u z) = -∫ z, φ z * v z := by
  let φr : 𝓓(Ω, ℝ) := TestFunction.postcompCLM Complex.reCLM φ
  let φi : 𝓓(Ω, ℝ) := TestFunction.postcompCLM Complex.imCLM φ
  have hr := h.integral_lineDeriv_smul_eq_neg_integral_smul φr
  have hi := h.integral_lineDeriv_smul_eq_neg_integral_smul φi
  have hdr (z : ℂ) : lineDeriv ℝ (φr : ℂ → ℝ) z d =
      (lineDeriv ℝ (φ : ℂ → ℂ) z d).re :=
    lineDeriv_postcomp (φ.contDiff.differentiable (by norm_num) z) Complex.reCLM d
  have hdi (z : ℂ) : lineDeriv ℝ (φi : ℂ → ℝ) z d =
      (lineDeriv ℝ (φ : ℂ → ℂ) z d).im :=
    lineDeriv_postcomp (φ.contDiff.differentiable (by norm_num) z) Complex.imCLM d
  have hAr := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φr d
  have hAi := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn φi d
  have hBr := TauCeti.integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φr
  have hBi := TauCeti.integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv φi
  have hA : (fun z => lineDeriv ℝ (φ : ℂ → ℂ) z d * u z) =
      fun z => lineDeriv ℝ (φr : ℂ → ℝ) z d • u z +
        Complex.I * (lineDeriv ℝ (φi : ℂ → ℝ) z d • u z) := by
    funext z
    rw [hdr, hdi]
    simp only [Complex.real_smul]
    rw [← mul_assoc, ← add_mul, mul_comm Complex.I, Complex.re_add_im]
  have hB : (fun z => φ z * v z) =
      fun z => φr z • v z + Complex.I * (φi z • v z) := by
    funext z
    change φ z * v z = (φ z).re • v z + Complex.I * ((φ z).im • v z)
    simp only [Complex.real_smul]
    rw [← mul_assoc, ← add_mul, mul_comm Complex.I, Complex.re_add_im]
  rw [hA, hB, integral_add hAr (hAi.const_mul Complex.I),
    integral_add hBr (hBi.const_mul Complex.I), integral_const_mul, integral_const_mul,
    hr, hi]
  ring

/-- Smooth compact multiplication packages a valid complex test on Ω. -/
def cutoffTest {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : 𝓓(Ω, ℂ) :=
  ⟨fun z => χ z • φ z, hχ.smul hφ, hc.smul_right,
    (tsupport_smul_subset_left χ φ).trans hs⟩

/-- One cutoff suffices: apply weak IBP to χφ and expand its derivative.
The Schwartz test class is a special case; no second cutoff is needed. -/
theorem localized_integral_lineDeriv_mul {Ω : Opens ℂ} {u v : ℂ → ℂ} {d : ℂ}
    (h : TauCeti.HasWeakLineDerivOn volume Ω u v d) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (∫ z, lineDeriv ℝ φ z d * (χ z • u z)) =
      -∫ z, φ z * (χ z • v z + fderiv ℝ χ z d • u z) := by
  let ψ := cutoffTest hχ hc hs hφ
  have hdiff : ∀ z, lineDeriv ℝ (ψ : ℂ → ℂ) z d =
      fderiv ℝ χ z d • φ z + χ z • fderiv ℝ φ z d := by
    intro z
    change lineDeriv ℝ (χ • φ) z d = _
    simpa only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, add_comm] using
      (((hχ.differentiable (by simp) z).hasFDerivAt.smul
      (hφ.differentiable (by simp) z).hasFDerivAt).hasLineDerivAt d).lineDeriv
  have hχd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ χ z d) :=
    (contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const
  have hφd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z d) :=
    (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  let ψA := cutoffTest hχ hc hs hφd
  let ψB := cutoffTest hχd (hc.fderiv_apply (𝕜 := ℝ) d)
    ((tsupport_fderiv_apply_subset ℝ d).trans hs) hφ
  have hA := ψA.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) h.locallyIntegrableOn
  have hB := ψB.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) h.locallyIntegrableOn
  have hC := ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) h.locallyIntegrableOn_deriv
  change Integrable (fun z => ψA z * u z) at hA
  change Integrable (fun z => ψB z * u z) at hB
  change Integrable (fun z => ψ z * v z) at hC
  have he := integral_lineDeriv_mul_eq_neg h ψ
  simp_rw [hdiff, add_mul] at he
  change (∫ z, ψB z * u z + ψA z * u z) = -∫ z, ψ z * v z at he
  rw [integral_add hB hA] at he
  have htarget : (fun z => φ z * (χ z • v z + fderiv ℝ χ z d • u z)) =
      fun z => ψ z * v z + ψB z * u z := by
    funext z
    change φ z * (χ z • v z + fderiv ℝ χ z d • u z) =
      (χ z • φ z) * v z + (fderiv ℝ χ z d • φ z) * u z
    simp only [Complex.real_smul]
    ring
  have hleft : (fun z => lineDeriv ℝ φ z d * (χ z • u z)) =
      fun z => ψA z * u z := by
    funext z
    rw [(hφ.differentiable (by simp) z).lineDeriv_eq_fderiv]
    change fderiv ℝ φ z d * (χ z • u z) = (χ z • fderiv ℝ φ z d) * u z
    simp only [Complex.real_smul]
    ring
  rw [htarget, hleft, integral_add hC hB]
  linear_combination he

end KsIndex.WeakComplexTest
