module

public import KsIndexLean.SphericalChartMeasure
public import KsIndexLean.Bracket
public import KsIndexLean.SigmaDeriv
public import Mathlib.LinearAlgebra.Complex.Determinant

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical

lemma real_det_antilinear (J : ℂ →L[ℝ] ℂ) (a : ℂ)
    (h : ∀ v, J v = a * (starRingEnd ℂ) v) : J.toLinearMap.det = -‖a‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, h, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

lemma abs_det_sigma {z : ℂ} (hz : z ≠ 0) :
    |(fderiv ℝ Bracket.σ z).toLinearMap.det| = ‖z‖⁻¹ ^ 4 := by
  have h := real_det_antilinear (fderiv ℝ Bracket.σ z)
    (-(((starRingEnd ℂ) z) ^ 2)⁻¹) (fun v => SigmaDeriv.fderiv_sigmaR_apply hz v)
  rw [h]
  simp [norm_inv, norm_pow]
  ring

lemma stereoAreaDensity_sigma {z : ℂ} (hz : z ≠ 0) :
    stereoAreaDensity (Bracket.σ z) * ‖z‖⁻¹ ^ 4 = stereoAreaDensity z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [stereoAreaDensity_eq, stereoAreaDensity_eq, Bracket.norm_σ]
  field_simp
  ring

lemma stereoAreaDensity_jacobian {z : ℂ} (hz : z ≠ 0) :
    |(fderiv ℝ Bracket.σ z).toLinearMap.det| * stereoAreaDensity (Bracket.σ z) =
      stereoAreaDensity z := by
  rw [abs_det_sigma hz, mul_comm, stereoAreaDensity_sigma hz]

end KsIndex.Spherical
