module

public import KsIndexLean.KarcherChartArea
public import KsIndexLean.SphericalWeakJacobi
public import KsIndexLean.ExplicitModeJacobi

@[expose] public section

noncomputable section
open Filter Topology
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.KarcherData KsIndex.JacobiMode KsIndex.Trace

/-- The coefficient in the chart operator is the pullback of the round metric. -/
lemma sphericalChart_metric_coefficient (z v w : ℂ) :
    inner ℝ (fderiv ℝ stereoPoint z v) (fderiv ℝ stereoPoint z w) =
      stereoAreaDensity z * inner ℝ v w := by
  rw [stereoAreaDensity_eq, fderiv_stereoPoint_inner]

/-- The spherical Schrödinger operator in stereographic coordinates, using
Laplace–Beltrami in divergence form and the canonical spherical potential. -/
def sphericalChartJacobiOperator (k : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conformalLaplaceBeltrami stereoAreaDensity f z +
    (spherePotential (surfacePotential k) (sphereChart z) : ℂ) * f z

lemma sphericalChartJacobiOperator_eq (k : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    sphericalChartJacobiOperator k f z = (stereoAreaDensity z : ℂ)⁻¹ *
      (Surface.laplacian f z + (Surface.potV k z : ℂ) * f z) := by
  unfold sphericalChartJacobiOperator
  rw [conformalLaplaceBeltrami_eq (Eventually.of_forall
    (fun w => ne_of_gt (stereoAreaDensity_pos w))), spherePotential_pullback]
  change (stereoAreaDensity z : ℂ)⁻¹ * Surface.laplacian f z +
    ((Surface.potV k z / stereoAreaDensity z : ℝ) : ℂ) * f z = _
  push_cast
  ring

/-- The explicit radial mode is a classical spherical Jacobi field in the chart. -/
theorem sphericalChartJacobiOperator_mode_zero {k : ℕ} (hk : 2 ≤ k) (z : ℂ) :
    sphericalChartJacobiOperator k (modeU k 0) z = 0 := by
  rw [sphericalChartJacobiOperator_eq, modeU_jacobi hk 0 z, mul_zero]

/-- Its boundary value vanishes pointwise on the equator. -/
theorem spherical_radial_mode_equator {k : ℕ} (hk : 2 ≤ k)
    (p : Sphere) (hp : p.val 2 = 0) : modeU k 0 (stereoCoord p.val) = 0 := by
  have he := stereoCoord_norm_sq p (by rw [hp]; norm_num)
  have hn : ‖stereoCoord p.val‖ = 1 := by
    rw [hp] at he
    norm_num at he
    rcases he with he | he
    · exact he
    · have := norm_nonneg (stereoCoord p.val)
      linarith
  rw [modeU, hn, Radial.gRad_zero_one hk]
  simp
end KsIndex.Spherical
