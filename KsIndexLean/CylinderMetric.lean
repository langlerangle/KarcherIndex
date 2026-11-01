module

public import KsIndexLean.CylinderLaplacian
public import KsIndexLean.KarcherBoundaryConormal
public import KsIndexLean.SphericalGlobalOperator

@[expose] public section


/-! Flat cylindrical and round spherical metrics in logarithmic coordinates. -/
noncomputable section
open Set Topology
namespace KsIndex.Cylindrical
open KarcherData Spherical

/-- The metric of the logarithmic cylinder in the punctured plane. -/
def cylinderDensity (z : ℂ) : ℝ := (‖z‖ ^ 2)⁻¹

lemma expDifferential_norm_sq (z v : ℂ) :
    ‖expDifferential z v‖ ^ 2 = ‖Complex.exp z‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [expDifferential_apply, norm_mul, mul_pow]

/-- Pulling the cylindrical metric back by the exponential gives the flat metric. -/
theorem cylinderDensity_exp_metric (z v : ℂ) :
    cylinderDensity (Complex.exp z) * ‖fderiv ℝ Complex.exp z v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [(hasFDerivAt_exp_real z).fderiv, expDifferential_norm_sq, cylinderDensity]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (Complex.exp_ne_zero z))), one_mul]

/-- The cylindrical and spherical metrics agree on the equator. -/
lemma cylinderDensity_eq_round_on_unit {z : ℂ} (hz : ‖z‖ = 1) :
    cylinderDensity z = stereoAreaDensity z := by
  norm_num [cylinderDensity, stereoAreaDensity_eq, hz]

/-- Radial and angular logarithmic directions form an orthonormal frame for
the cylindrical metric; at the unit circle the radial direction is outward. -/
theorem cylinder_radial_conormal {z : ℂ} (hz : ‖z‖ = 1) :
    cylinderDensity z * ‖z‖ ^ 2 = 1 ∧
    cylinderDensity z * inner ℝ z (z * Complex.I) = 0 ∧
    stereoAreaDensity z * ‖z‖ ^ 2 = 1 := by
  have ho : inner ℝ z (z * Complex.I) = 0 := by
    simp [inner]
    ring
  norm_num [cylinderDensity, stereoAreaDensity_eq, hz, ho]

/-- Increasing the real logarithmic coordinate crosses the unit circle outwards. -/
lemma exp_time_outward (t θ : ℝ) :
    ‖Complex.exp ((t : ℂ) + θ * Complex.I)‖ ≤ 1 ↔ t ≤ 0 := by
  rw [Complex.norm_exp]
  simp

namespace ActualMetric
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The actual EW immersion metric, rescaled as in the paper, is flat in
logarithmic coordinates. -/
theorem centeredChart_cylinder_metric (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (ζ : ℂ)
    (he : Complex.exp ζ = w.val) (v : ℂ) :
    (‖w.val‖ ^ 2 * Surface.rho k w.val ^ 2)⁻¹ *
      euclideanSq (fderiv ℝ (R.centeredChart q) w.val (expDifferential ζ v)) = ‖v‖ ^ 2 := by
  rw [(R.centeredChart_finite_metric_field q w hq).self_of_nhds,
    expDifferential_norm_sq, he]
  have hr := ne_of_gt (Surface.rho_pos (by have := h.out; omega) w.property)
  have hn : ‖w.val‖ ≠ 0 := norm_ne_zero_iff.mpr (he ▸ Complex.exp_ne_zero ζ)
  field_simp [hr]

/-- On the half-period boundary the unnormalized radial pushforward is unit
and orthogonal to the boundary tangent in the cylindrical rescaling. -/
theorem centeredChart_cylinder_conormal (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (hw : ‖w.val‖ = 1) :
    let D := fderiv ℝ (R.centeredChart q) w.val
    let a := (‖w.val‖ ^ 2 * Surface.rho k w.val ^ 2)⁻¹
    a * euclideanSq (D w.val) = 1 ∧
      a * euclideanDot (D w.val) (D (w.val * Complex.I)) = 0 := by
  have hm := (R.centeredChart_finite_metric_field q w hq).self_of_nhds
  dsimp only
  constructor
  · rw [hm, hw]
    have hr : Surface.rho k w.val ^ 2 ≠ 0 := ne_of_gt (rho_sq_pos h.out w.property)
    simp [hr]
  · rw [conformal_radial_tangent hm hw, mul_zero]

end ActualMetric
end KsIndex.Cylindrical
