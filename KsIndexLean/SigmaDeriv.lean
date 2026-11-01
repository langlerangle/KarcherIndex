module

/-
Real derivative of the circle reflection σ(z) = 1/conj(z).

Away from zero, its derivative sends h to -(conj(z)^2)⁻¹ * conj(h).
On the unit circle this reverses the radial direction and preserves the
angular tangent. These signs enter the normal-flux calculation across the seam.

The derivative is expressed as complex inversion, restricted to real scalars,
composed with real-linear conjugation.
-/
public import Mathlib

@[expose] public section


open Complex

noncomputable section

namespace KsIndex.SigmaDeriv

/-- The Fréchet derivative of the reflection `σ(z) = 1/z̄` at `w ≠ 0`, as a real-linear map:
the ℂ-derivative of inversion at `w̄` (an ℝ-restricted `toSpanSingleton`) composed with the
ℝ-linear conjugation `conjCLE`.  `σ = inv ∘ conj`. -/
theorem hasFDerivAt_sigmaR {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => 1 / (starRingEnd ℂ) z)
      (((ContinuousLinearMap.toSpanSingleton ℂ
            (-(((starRingEnd ℂ) w) ^ 2)⁻¹)).restrictScalars ℝ).comp
        (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ)) w := by
  have hconjw : (starRingEnd ℂ) w ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hw
  -- inner: conjugation, ℝ-linear, its own derivative
  have hf : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z)
      (Complex.conjCLE.toContinuousLinearMap : ℂ →L[ℝ] ℂ) w := by
    have hfun : (fun z : ℂ => (starRingEnd ℂ) z) = ⇑Complex.conjCLE := by
      funext z; rw [Complex.conjCLE_apply]
    rw [hfun]; exact Complex.conjCLE.hasFDerivAt
  -- outer: ℂ-inversion at `w̄`, restricted to ℝ
  have hg : HasFDerivAt (fun y : ℂ => y⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ
          (-(((starRingEnd ℂ) w) ^ 2)⁻¹)).restrictScalars ℝ) ((starRingEnd ℂ) w) :=
    ((hasDerivAt_inv hconjw).hasFDerivAt).restrictScalars ℝ
  -- compose (`1/z̄` = `inv ∘ conj`)
  have hfun : (fun z : ℂ => 1 / (starRingEnd ℂ) z)
      = (fun y : ℂ => y⁻¹) ∘ (fun z : ℂ => (starRingEnd ℂ) z) := by
    funext z; simp [Function.comp, one_div]
  rw [hfun]
  exact hg.comp w hf

/-- Pointwise derivative formula: `fderiv ℝ σ w h = −(w̄²)⁻¹ · h̄`. -/
lemma fderiv_sigmaR_apply {w : ℂ} (hw : w ≠ 0) (h : ℂ) :
    fderiv ℝ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w h
      = -(((starRingEnd ℂ) w) ^ 2)⁻¹ * (starRingEnd ℂ) h := by
  rw [(hasFDerivAt_sigmaR hw).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, smul_eq_mul]
  ring

/-- The radial direction reverses on the unit circle: `dσ_w(w) = −w` (the outward normal reverses). -/
lemma fderiv_sigmaR_radial {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w w = -w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have key : (starRingEnd ℂ) w * w = 1 := by rw [Complex.conj_mul', hw]; norm_num
  have hinv : ((starRingEnd ℂ) w)⁻¹ = w := inv_eq_of_mul_eq_one_right key
  rw [fderiv_sigmaR_apply hw0, ← inv_pow, hinv]
  linear_combination (-w) * key

/-- The tangential direction is preserved on `‖w‖ = 1`: `dσ_w(iw) = iw` (the tangent is preserved). -/
lemma fderiv_sigmaR_tangential {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (fun z : ℂ => 1 / (starRingEnd ℂ) z) w (Complex.I * w) = Complex.I * w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have key : (starRingEnd ℂ) w * w = 1 := by rw [Complex.conj_mul', hw]; norm_num
  have hinv : ((starRingEnd ℂ) w)⁻¹ = w := inv_eq_of_mul_eq_one_right key
  rw [fderiv_sigmaR_apply hw0, map_mul, Complex.conj_I, ← inv_pow, hinv]
  linear_combination (Complex.I * w) * key

end KsIndex.SigmaDeriv
