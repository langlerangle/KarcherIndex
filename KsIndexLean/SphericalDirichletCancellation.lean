module

public import KsIndexLean.SphericalGradientLift
public import KsIndexLean.SphericalWeightedIntegrals

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

/-- Canonical spherical energy equals planar energy for corresponding chart gradients. -/
theorem lintegral_dirichlet_of_chart (A : Set Sphere) (hA : MeasurableSet A)
    (V : Sphere → Ambient) (hV : Measurable V) (v : ℂ → ℂ)
    (hv : ∀ z ∈ sphereChart ⁻¹' A, V (sphereChart z) = gradientLift z (v z)) :
    ∫⁻ p in A, ENNReal.ofReal (‖V p‖ ^ 2) ∂(volume : Measure Ambient).toSphere =
      ∫⁻ z in sphereChart ⁻¹' A, ENNReal.ofReal (‖v z‖ ^ 2) ∂volume := by
  rw [setLIntegral_sphere_weight A hA _ (by fun_prop)]
  apply setLIntegral_congr_fun (hA.preimage continuous_sphereChart.measurable)
  intro z hz
  dsimp only
  rw [hv z hz, ← stereoAreaDensity_eq,
    ← ENNReal.ofReal_mul (le_of_lt (stereoAreaDensity_pos z)), gradientLift_norm_sq_cancel]

/-- Bilinear Dirichlet cancellation; real pairings are embedded in ℂ for the integral API. -/
theorem integral_dirichlet_pairing_of_chart (A : Set Sphere) (hA : MeasurableSet A)
    (V W : Sphere → Ambient) (hV : Measurable V) (hW : Measurable W)
    (v w : ℂ → ℂ)
    (hv : ∀ z ∈ sphereChart ⁻¹' A, V (sphereChart z) = gradientLift z (v z))
    (hw : ∀ z ∈ sphereChart ⁻¹' A, W (sphereChart z) = gradientLift z (w z)) :
    ∫ p in A, (inner ℝ (V p) (W p) : ℂ) ∂(volume : Measure Ambient).toSphere =
      ∫ z in sphereChart ⁻¹' A, (inner ℝ (v z) (w z) : ℂ) ∂volume := by
  rw [setIntegral_sphere_weight A hA _ (by fun_prop)]
  apply setIntegral_congr_fun (hA.preimage continuous_sphereChart.measurable)
  intro z hz
  dsimp only
  rw [hv z hz, hw z hz, ← stereoAreaDensity_eq]
  change ((stereoAreaDensity z : ℂ) * (inner ℝ (gradientLift z (v z))
    (gradientLift z (w z)) : ℂ)) = _
  rw [← Complex.ofReal_mul, gradientLift_inner_cancel]

end KsIndex.Spherical
