module

public import KsIndexLean.KarcherChartMetricField

@[expose] public section


/-! Unit outward conormals on a conformally parametrized disk boundary.
The ambient length is the Euclidean length of the immersion, rather than
 the product norm on triples. -/
noncomputable section
namespace KsIndex.KarcherData

/-- The pushforward of the outward radial coordinate, normalized in the
induced metric. This definition is used with a positive conformal factor. -/
def boundaryConormal (D : ℂ →L[ℝ] AmbientTriple) (ρ : ℝ) (w : ℂ) : AmbientTriple :=
  ρ⁻¹ • D w

/-- On the unit circle the radial vector is orthogonal to the circle tangent
for a conformal induced metric. -/
lemma conformal_radial_tangent {D : ℂ →L[ℝ] AmbientTriple} {ρ : ℝ} {w : ℂ}
    (hm : ∀ d, euclideanSq (D d) = ρ ^ 2 * ‖d‖ ^ 2) (hw : ‖w‖ = 1) :
    euclideanDot (D w) (D (w * Complex.I)) = 0 := by
  let M : ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ w
  have hM (d : ℂ) : M d = w * d := rfl
  have h : ∀ d, euclideanSq ((D.comp M) d) = ρ ^ 2 * ‖d‖ ^ 2 := by
    intro d
    simp only [ContinuousLinearMap.comp_apply, hM, hm, norm_mul, hw, one_mul]
  have hh := (metric_coefficients_of_conformal h).2.1
  simpa only [ContinuousLinearMap.comp_apply, hM, mul_one] using hh

/-- Unit length, tangency to the immersed surface, and positive outward
orientation are certified by the normalized radial pushforward. -/
theorem boundaryConormal_spec {D : ℂ →L[ℝ] AmbientTriple} {ρ : ℝ} {w : ℂ}
    (hρ : 0 < ρ) (hm : ∀ d, euclideanSq (D d) = ρ ^ 2 * ‖d‖ ^ 2)
    (hw : ‖w‖ = 1) :
    euclideanSq (boundaryConormal D ρ w) = 1 ∧
    euclideanDot (boundaryConormal D ρ w) (D (w * Complex.I)) = 0 ∧
    boundaryConormal D ρ w = D (ρ⁻¹ • w) ∧ 0 < ρ⁻¹ := by
  refine ⟨?_, ?_, ?_, inv_pos.mpr hρ⟩
  · rw [boundaryConormal, euclideanSq_smul, hm, hw]
    field_simp
  · rw [boundaryConormal, euclideanDot_smul_left, conformal_radial_tangent hm hw,
      mul_zero]
  · simp only [boundaryConormal, map_smul]

/-- Multiplying the radial derivative by the positive reciprocal conformal
factor does not change the homogeneous Neumann condition. -/
theorem unit_conormal_derivative_zero_iff {ρ : ℝ} (hρ : 0 < ρ)
    (f : ℂ → ℂ) (w : ℂ) :
    fderiv ℝ f w (ρ⁻¹ • w) = 0 ↔ fderiv ℝ f w w = 0 := by
  rw [map_smul, smul_eq_zero]
  simp [ne_of_gt hρ]

open scoped KsIndex.KarcherData.ParameterAtlas KsIndex.KarcherData.PeriodicAmbient
namespace PaperHalfPeriodRealization
variable {k : ℕ} [h : Fact (2 ≤ k)]

/-- The unit conormal of the actual EW chart along the punctured unit circle
is its normalized radial derivative. -/
theorem centeredChart_boundaryConormal (R : PaperHalfPeriodRealization k)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (hw : ‖w.val‖ = 1) :
    let D := fderiv ℝ (R.centeredChart q) w.val
    let ρ := Surface.rho k w.val
    euclideanSq (boundaryConormal D ρ w.val) = 1 ∧
    euclideanDot (boundaryConormal D ρ w.val) (D (w.val * Complex.I)) = 0 ∧
    boundaryConormal D ρ w.val = D (ρ⁻¹ • w.val) ∧ 0 < ρ⁻¹ := by
  exact boundaryConormal_spec (Surface.rho_pos (by have := h.out; omega) w.property)
    (R.centeredChart_finite_metric_field q w hq).self_of_nhds hw

end PaperHalfPeriodRealization
end KsIndex.KarcherData
