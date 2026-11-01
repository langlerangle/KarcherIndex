module

public import KsIndexLean.CylinderCoordinates
public import KsIndexLean.CylinderLaplacian
public import KsIndexLean.SphericalGlobalOperator
public import KsIndexLean.CylinderBoundedModes

@[expose] public section


/-! The cylindrical Schrödinger operator, its logarithmic-coordinate formula,
and its pointwise relation with the spherical operator. -/
noncomputable section
open Set Topology
open scoped ContDiff
namespace KsIndex.Cylindrical
open Spherical KarcherData

/-- A cylinder function represented on the punctured plane; its value at zero
is irrelevant to every operator identity below. -/
def planeRepresentative (U : Cylinder → ℂ) (z : ℂ) : ℂ :=
  if hz : z ≠ 0 then U (logarithmicHomeomorph ⟨z, hz⟩) else 0

lemma planeRepresentative_apply (U : Cylinder → ℂ) {z : ℂ} (hz : z ≠ 0) :
    planeRepresentative U z = U (logarithmicHomeomorph ⟨z, hz⟩) := dite_eq_left hz

/-- The global cylindrical operator represented in the punctured-plane chart.
Its local logarithmic expression is proved below. -/
def cylinderOperator (k : ℕ) (U : Cylinder → ℂ) (p : Cylinder) : ℂ :=
  let z := (logarithmicHomeomorph.symm p).val
  ((‖z‖ ^ 2 : ℝ) : ℂ) * Surface.laplacian (planeRepresentative U) z +
    (Radial.Vcyl k p.1 : ℂ) * U p

/-- The standard real logarithmic-coordinate cover of the cylinder. -/
def cylinderChart (ζ : ℂ) : Cylinder :=
  logarithmicHomeomorph ⟨Complex.exp ζ, Complex.exp_ne_zero ζ⟩

lemma cylinderChart_time (ζ : ℂ) : (cylinderChart ζ).1 = ζ.re := by
  simp [cylinderChart, logarithmicHomeomorph_time, Complex.norm_exp]

lemma cylinderChart_coordinates (t θ : ℝ) :
    cylinderChart ((t : ℂ) + θ * Complex.I) = (t, Circle.exp θ) := by
  apply logarithmicHomeomorph.symm.injective
  apply Subtype.ext
  simp only [cylinderChart, Homeomorph.symm_apply_apply, logarithmicHomeomorph_symm]
  simp [Complex.exp_add, Circle.coe_exp]

lemma planeRepresentative_comp_exp (U : Cylinder → ℂ) :
    planeRepresentative U ∘ Complex.exp = U ∘ cylinderChart := by
  funext z
  exact planeRepresentative_apply U (Complex.exp_ne_zero z)

/-- In logarithmic coordinates the principal part is ∂t² + ∂θ², and the
potential is exactly the paper's sech-squared coefficient. -/
theorem cylinderOperator_chart (k : ℕ) (U : Cylinder → ℂ) (ζ : ℂ)
    (hU : ContDiffAt ℝ 2 (planeRepresentative U) (Complex.exp ζ)) :
    cylinderOperator k U (cylinderChart ζ) =
      Surface.laplacian (U ∘ cylinderChart) ζ +
        (Radial.Vcyl k ζ.re : ℂ) * U (cylinderChart ζ) := by
  have he : (logarithmicHomeomorph.symm (cylinderChart ζ)).val = Complex.exp ζ := by
    simp [cylinderChart]
  rw [cylinderOperator, he, ← laplacian_comp_exp hU,
    planeRepresentative_comp_exp, cylinderChart_time]

/-- The algebraic radial potential agrees with the cylindrical potential
at the logarithmic radius. -/
lemma cylindrical_potential {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ 0) :
    ‖z‖ ^ 2 * Surface.potV k z = Radial.Vcyl k (Real.log ‖z‖) := by
  have h := Radial.Vrad_exp_eq hk (Real.log ‖z‖)
  rw [Real.exp_log (norm_pos_iff.mpr hz)] at h
  exact h

/-- The conformal factor in the paper's spherical–cylindrical identity. -/
def sphericalCylinderFactor (z : ℂ) : ℝ := (1 + ‖z‖ ^ 2)^2 / (4 * ‖z‖ ^ 2)

lemma sphericalCylinderFactor_density (z : ℂ) :
    sphericalCylinderFactor z = (stereoAreaDensity z * ‖z‖ ^ 2)⁻¹ := by
  simp only [sphericalCylinderFactor, stereoAreaDensity_eq, div_eq_mul_inv, mul_inv_rev,
    inv_inv]
  ring

lemma sphericalCylinderFactor_unit {z : ℂ} (hz : ‖z‖ = 1) :
    sphericalCylinderFactor z = 1 := by norm_num [sphericalCylinderFactor, hz]

/-- Full pointwise spherical–cylindrical operator identity on the punctured plane. -/
theorem spherical_cylinder_intertwine {k : ℕ} (hk : 2 ≤ k) (U : Cylinder → ℂ)
    {z : ℂ} (hz : z ≠ 0) :
    sphericalChartJacobiOperator k (planeRepresentative U) z =
      (sphericalCylinderFactor z : ℂ) *
        cylinderOperator k U (logarithmicHomeomorph ⟨z, hz⟩) := by
  rw [sphericalChartJacobiOperator_eq, cylinderOperator,
    Homeomorph.symm_apply_apply, logarithmicHomeomorph_time,
    ← cylindrical_potential hk hz, planeRepresentative_apply U hz,
    sphericalCylinderFactor_density]
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  have hd : (stereoAreaDensity z : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (stereoAreaDensity_pos z)
  push_cast
  field_simp [hn, hd]

/-- The same identity for the already defined global spherical operator. -/
theorem sphereJacobi_cylinder_pullback {k : ℕ} (hk : 2 ≤ k) (U : Cylinder → ℂ)
    (F : Sphere → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hF : F ∘ sphereChart =ᶠ[𝓝 z] planeRepresentative U) :
    sphereJacobiOperator k F (sphereChart z) =
      (sphericalCylinderFactor z : ℂ) *
        cylinderOperator k U (logarithmicHomeomorph ⟨z, hz⟩) := by
  rw [sphereJacobiOperator_finite, sphericalChartJacobiOperator_congr hF]
  exact spherical_cylinder_intertwine hk U hz

end KsIndex.Cylindrical
