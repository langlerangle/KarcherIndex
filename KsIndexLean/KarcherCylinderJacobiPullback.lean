module

public import KsIndexLean.CylinderOperator
public import KsIndexLean.KarcherSphericalJacobiPullback

@[expose] public section


/-! Cylindrical conformal normalization of the actual EW Jacobi operator. -/
noncomputable section
open Set Topology Filter
open scoped ContDiff Manifold KsIndex.KarcherData.ParameterAtlas
namespace KsIndex.KarcherData
open Spherical Cylindrical

/-- The cylindrical normalization of the geometric operator in a finite EW chart. -/
lemma diskJacobi_cylinder_rescale {k : ℕ} (hk : 2 ≤ k) (U : Cylinder → ℂ)
    {z : ℂ} (hz : z ≠ 0) (hp : z ∉ Surface.punctures k) :
    ((‖z‖ ^ 2 * Surface.rho k z ^ 2 : ℝ) : ℂ) *
      diskJacobi k (planeRepresentative U) z =
      cylinderOperator k U (logarithmicHomeomorph ⟨z, hz⟩) := by
  rw [diskJacobi_eq_flat hk hp]
  simp only [cylinderOperator, Homeomorph.symm_apply_apply]
  rw [logarithmicHomeomorph_time, ← cylindrical_potential hk hz, planeRepresentative_apply U hz]
  have hr : (Surface.rho k z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Surface.rho_pos (by omega) hp))
  push_cast
  field_simp [hr]

/-- A total spherical representative; its values at the excluded poles play no
role in cylindrical-coordinate identities. -/
def cylinderSphereRepresentative (U : Cylinder → ℂ) (p : Sphere) : ℂ :=
  planeRepresentative U (stereoCoord p.val)

lemma cylinderSphereRepresentative_chart (U : Cylinder → ℂ) :
    cylinderSphereRepresentative U ∘ sphereChart = planeRepresentative U := by
  funext z
  simp [cylinderSphereRepresentative, sphereChart,
    stereoCoord_stereoPoint]

namespace PaperHalfPeriodRealization
variable {k m : ℕ} [h : Fact (2 ≤ k)] (R : PaperHalfPeriodRealization k)

/-- The full cylindrical operator is the conformally rescaled geometric Jacobi
operator on every actual EW quotient chart away from the two parameter poles. -/
theorem geometricJacobiAt_cylinder_pullback (U : Cylinder → ℂ)
    (q : PeriodicEWCarrier h.out (reflectionBasepoint k) R.C) (w : PuncturedPlane k)
    (hq : HeightLift.projection q = finiteParameter w) (hw : w.val ≠ 0) :
    ((‖w.val‖ ^ 2 * Surface.rho k w.val ^ 2 : ℝ) : ℂ) *
      R.geometricJacobiAt
        (cylinderSphereRepresentative U ∘ R.sphericalProjection (m := m)) q =
      cylinderOperator k U (logarithmicHomeomorph ⟨w.val, hw⟩) := by
  rw [R.geometricJacobiAt_eq_diskJacobi, R.chartCenter_finite q w hq,
    diskJacobi_congr (R.sphericalPullback_finite_germ (m := m)
      (cylinderSphereRepresentative U) q w hq), cylinderSphereRepresentative_chart]
  exact diskJacobi_cylinder_rescale h.out U hw w.property

end PaperHalfPeriodRealization
end KsIndex.KarcherData
