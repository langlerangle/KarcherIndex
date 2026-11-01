module

public import KsIndexLean.PolarPullback

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped Distributions ContDiff

noncomputable section
namespace KsIndex.Trace

lemma complex_rotation_decomp (z : ℂ) :
    z * Complex.I = (-z.im) • (1 : ℂ) + z.re • Complex.I := by
  apply Complex.ext <;> simp [Complex.real_smul]

/-- Angular coordinate derivative, including the radius in the tangent zI. -/
def angularField (U : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) : ℂ :=
  (-z.im) • U z 1 + z.re • U z Complex.I

lemma angularField_apply (U : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) :
    angularField U z = U z (z * Complex.I) := by
  rw [complex_rotation_decomp, map_add, map_smul, map_smul]
  rfl

/-- Coordinate multiplication preserves the original compact test support. -/
def linearWeightedTest {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ) (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨fun z => L z * φ z, L.contDiff.mul φ.contDiff, φ.hasCompactSupport.mul_left,
    tsupport_mul_subset_right.trans φ.tsupport_subset⟩

lemma lineDeriv_linearWeightedTest {Ω : Opens ℂ} (L : ℂ →L[ℝ] ℝ)
    (φ : 𝓓(Ω, ℝ)) (z v : ℂ) (hv : L v = 0) :
    lineDeriv ℝ (linearWeightedTest L φ : ℂ → ℝ) z v =
      L z * lineDeriv ℝ (φ : ℂ → ℝ) z v := by
  have hf := φ.contDiff.differentiable (by simp) z
  have hd := L.hasFDerivAt.mul hf.hasFDerivAt
  change lineDeriv ℝ ((L : ℂ → ℝ) * (φ : ℂ → ℝ)) z v = _
  rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv,
    hf.lineDeriv_eq_fderiv]
  simp [hv, mul_comm]

/-- The angular weak identity comes from two constant-direction identities;
no variable-direction weak-derivative principle is assumed. -/
theorem weak_angular_generator {Ω : Opens ℂ} {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U) (φ : 𝓓(Ω, ℝ)) :
    (∫ z, fderiv ℝ (φ : ℂ → ℝ) z (z * Complex.I) • u z) =
      -∫ z, φ z • angularField U z := by
  let ψx := linearWeightedTest Complex.imCLM φ
  let ψy := linearWeightedTest Complex.reCLM φ
  have hx := (hw.hasWeakLineDerivOn 1).integral_lineDeriv_smul_eq_neg_integral_smul ψx
  have hy := (hw.hasWeakLineDerivOn Complex.I).integral_lineDeriv_smul_eq_neg_integral_smul ψy
  have hxi := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    (hw.hasWeakLineDerivOn 1).locallyIntegrableOn ψx 1
  have hyi := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
    (hw.hasWeakLineDerivOn Complex.I).locallyIntegrableOn ψy Complex.I
  have hxr := TauCeti.integrable_smul_of_locallyIntegrableOn
    (hw.hasWeakLineDerivOn 1).locallyIntegrableOn_deriv ψx
  have hyr := TauCeti.integrable_smul_of_locallyIntegrableOn
    (hw.hasWeakLineDerivOn Complex.I).locallyIntegrableOn_deriv ψy
  have hs : (∫ z, (lineDeriv ℝ (ψy : ℂ → ℝ) z Complex.I • u z -
      lineDeriv ℝ (ψx : ℂ → ℝ) z 1 • u z)) =
      -∫ z, ((ψy : ℂ → ℝ) z • U z Complex.I - (ψx : ℂ → ℝ) z • U z 1) := by
    rw [integral_sub hyi hxi, integral_sub hyr hxr, hy, hx, neg_sub_neg]
    abel
  have hl : (fun z => lineDeriv ℝ (ψy : ℂ → ℝ) z Complex.I • u z -
      lineDeriv ℝ (ψx : ℂ → ℝ) z 1 • u z) =
      (fun z => fderiv ℝ (φ : ℂ → ℝ) z (z * Complex.I) • u z) := by
    funext z
    rw [lineDeriv_linearWeightedTest Complex.reCLM φ z Complex.I (by simp),
      lineDeriv_linearWeightedTest Complex.imCLM φ z 1 (by simp)]
    have hf := φ.contDiff.differentiable (by simp) z
    rw [hf.lineDeriv_eq_fderiv, hf.lineDeriv_eq_fderiv,
      complex_rotation_decomp, map_add, map_smul, map_smul]
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul,
      neg_mul, add_smul, neg_smul, sub_eq_add_neg]
    abel
  have hr : (fun z => (ψy : ℂ → ℝ) z • U z Complex.I -
      (ψx : ℂ → ℝ) z • U z 1) = (fun z => φ z • angularField U z) := by
    funext z
    change (z.re * φ z) • U z Complex.I - (z.im * φ z) • U z 1 =
      φ z • ((-z.im) • U z 1 + z.re • U z Complex.I)
    rw [smul_add, smul_smul, smul_smul, mul_neg, neg_smul]
    rw [mul_comm (φ z) z.re, mul_comm (φ z) z.im]
    abel
  rw [hl, hr] at hs
  exact hs

end KsIndex.Trace
