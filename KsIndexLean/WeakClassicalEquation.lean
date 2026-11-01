module

public import KsIndexLean.WeakInteriorSmooth
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section


/-! Classical divergence equations from the concrete bilinear weak equation. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
namespace KsIndex.Weq

lemma smooth_hasWeakFDerivOn {Ω : Opens ℂ} {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set ℂ)) :
    TauCeti.HasWeakFDerivOn volume Ω f (fderiv ℝ f) :=
  TauCeti.hasWeakFDerivOn_of_differentiableOn
    (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    ((hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).locallyIntegrableOn
      Ω.isOpen.measurableSet)
    (fun z hz => (hf.contDiffAt (Ω.isOpen.mem_nhds hz)).differentiableAt (by simp))

/-- A continuous residual whose compact test integrals vanish is zero at every
point of the open coordinate domain, not merely almost everywhere. -/
lemma continuous_eq_zero_of_test_integrals {Ω : Opens ℂ} {R : ℂ → ℂ}
    (hR : ContinuousOn R (Ω : Set ℂ))
    (ht : ∀ ψ : 𝓓(Ω, ℂ), (∫ z, ψ z * R z) = 0) :
    ∀ z ∈ (Ω : Set ℂ), R z = 0 := by
  have ha := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hR.locallyIntegrableOn Ω.isOpen.measurableSet) (fun φ hf hc hs => by
      let ψ : 𝓓(Ω, ℝ) := ⟨φ, hf, hc, hs⟩
      have hh := ht (TestFunction.postcompCLM Complex.ofRealCLM ψ)
      change (∫ z, (φ z : ℂ) * R z) = 0 at hh
      simpa only [Complex.real_smul] using hh)
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' Ω.isOpen.measurableSet).mpr ha)
    Ω.isOpen hR continuousOn_const

/-- Smooth weak gradient components satisfy the pointwise divergence equation
with the same sign as the paper's Jacobi equation: `div grad = -q`. -/
theorem classical_divergence_of_interiorWeakEquation {Ω : Opens ℂ}
    {ux uy q : ℂ → ℂ}
    (hx : ContDiffOn ℝ (⊤ : ℕ∞) ux (Ω : Set ℂ))
    (hy : ContDiffOn ℝ (⊤ : ℕ∞) uy (Ω : Set ℂ))
    (hq : ContinuousOn q (Ω : Set ℂ))
    (heq : InteriorWeakEquation Ω ux uy q) :
    ∀ z ∈ (Ω : Set ℂ), fderiv ℝ ux z 1 + fderiv ℝ uy z Complex.I = -q z := by
  let X := fun z => fderiv ℝ ux z 1
  let Y := fun z => fderiv ℝ uy z Complex.I
  have hX : ContinuousOn X (Ω : Set ℂ) :=
    (hx.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hY : ContinuousOn Y (Ω : Set ℂ) :=
    (hy.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const
  have hz := continuous_eq_zero_of_test_integrals ((hX.add hY).add hq) (fun ψ => by
    have wx := (smooth_hasWeakFDerivOn hx).hasWeakLineDerivOn 1
    have wy := (smooth_hasWeakFDerivOn hy).hasWeakLineDerivOn Complex.I
    have ex := WeakComplexTest.integral_lineDeriv_mul_eq_neg wx ψ
    have ey := WeakComplexTest.integral_lineDeriv_mul_eq_neg wy ψ
    have hd (z d : ℂ) : lineDeriv ℝ (ψ : ℂ → ℂ) z d = fderiv ℝ (ψ : ℂ → ℂ) z d :=
      (ψ.contDiff.differentiable (by simp) z).lineDeriv_eq_fderiv
    simp_rw [hd] at ex ey
    have ix := (derivTest ψ 1).integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      wx.locallyIntegrableOn
    have iy := (derivTest ψ Complex.I).integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      wy.locallyIntegrableOn
    have iX := ψ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      (hX.locallyIntegrableOn Ω.isOpen.measurableSet)
    have iY := ψ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      (hY.locallyIntegrableOn Ω.isOpen.measurableSet)
    have iq := ψ.integrable_bilin (μ := volume) (ContinuousLinearMap.mul ℝ ℂ)
      (hq.locallyIntegrableOn Ω.isOpen.measurableSet)
    change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z 1 * ux z) at ix
    change Integrable (fun z => fderiv ℝ (ψ : ℂ → ℂ) z Complex.I * uy z) at iy
    change Integrable (fun z => ψ z * X z) at iX
    change Integrable (fun z => ψ z * Y z) at iY
    change Integrable (fun z => ψ z * q z) at iq
    have he := heq ψ
    rw [integral_add ix iy, ex, ey] at he
    change (∫ z, ψ z * ((X z + Y z) + q z)) = 0
    simp_rw [mul_add]
    have iXY : Integrable (fun z => ψ z * X z + ψ z * Y z) := iX.add iY
    rw [integral_add iXY iq, integral_add iX iY]
    change -(∫ z, ψ z * X z) + -(∫ z, ψ z * Y z) = ∫ z, ψ z * q z at he
    linear_combination -he)
  intro z hzo
  have hh := hz z hzo
  change (fderiv ℝ ux z 1 + fderiv ℝ uy z Complex.I) + q z = 0 at hh
  exact eq_neg_of_add_eq_zero_left hh

end KsIndex.Weq
