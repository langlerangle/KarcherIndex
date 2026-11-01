module

public import KsIndexLean.SphericalRadialGeometry
public import KsIndexLean.SphericalChartMeasure
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section


noncomputable section
namespace KsIndex.Spherical

/-- Tangential vector representing a planar gradient in the actual round metric. -/
def gradientLift (z v : ℂ) : Ambient :=
  (stereoAreaDensity z)⁻¹ • fderiv ℝ stereoPoint z v

lemma gradientLift_tangent (z v : ℂ) :
    inner ℝ (stereoPoint z) (gradientLift z v) = 0 := by
  simp [gradientLift, inner_smul_right, stereoPoint_inner_fderiv]

lemma gradientLift_represents (z v w : ℂ) :
    inner ℝ (gradientLift z v) (fderiv ℝ stereoPoint z w) = inner ℝ v w := by
  have hd := ne_of_gt (stereoAreaDensity_pos z)
  rw [gradientLift, inner_smul_left, fderiv_stereoPoint_inner, ← stereoAreaDensity_eq]
  simp [hd]

/-- The lifted actual gradient evaluates the differential on every chart tangent. -/
lemma gradientLift_gradient (f : ℂ → ℝ) (z w : ℂ) :
    inner ℝ (gradientLift z (gradient f z)) (fderiv ℝ stereoPoint z w) =
      fderiv ℝ f z w := by
  rw [gradientLift_represents, inner_gradient_left]

lemma gradientLift_inner_cancel (z v w : ℂ) :
    stereoAreaDensity z * inner ℝ (gradientLift z v) (gradientLift z w) =
      inner ℝ v w := by
  have hd := ne_of_gt (stereoAreaDensity_pos z)
  rw [gradientLift, gradientLift, inner_smul_left, inner_smul_right,
    fderiv_stereoPoint_inner, ← stereoAreaDensity_eq]
  simp [hd]

lemma gradientLift_norm_sq_cancel (z v : ℂ) :
    stereoAreaDensity z * ‖gradientLift z v‖ ^ 2 = ‖v‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using gradientLift_inner_cancel z v v

end KsIndex.Spherical
