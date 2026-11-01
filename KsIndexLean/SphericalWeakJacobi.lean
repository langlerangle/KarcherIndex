module

public import KsIndexLean.SphericalWeakPotential
public import KsIndexLean.WeakH1Integration

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

lemma integrable_sphereJacobi_pair (V : BoundedRealPotential) (u v : ComplexH1) :
    Integrable (fun p => tangentPair (sphereWeakGradient u p) (sphereWeakGradient v p) -
      (spherePotential V p : ℂ) * (starRingEnd ℂ) (sphereWeakValue u p) * sphereWeakValue v p)
      ((volume : Measure Ambient).toSphere.restrict (sphereChart '' (disk : Set ℂ))) :=
  (integrable_sphereWeak_pair u v).sub (integrable_spherePotential_pair V u v)

/-- The adopted weak Jacobi form as a finite canonical spherical chart integral. -/
theorem weakJacobi_eq_sphere_integral (V : BoundedRealPotential) (u v : ComplexH1) :
    weakJacobi V u v = ∫ p in sphereChart '' (disk : Set ℂ),
      tangentPair (sphereWeakGradient u p) (sphereWeakGradient v p) -
        (spherePotential V p : ℂ) * (starRingEnd ℂ) (sphereWeakValue u p) * sphereWeakValue v p
          ∂(volume : Measure Ambient).toSphere := by
  rw [weakJacobi, dirichlet_eq_sphere_integral, potential_eq_sphere_integral,
    integral_sub (integrable_sphereWeak_pair u v) (integrable_spherePotential_pair V u v)]

/-- Explicit spherical-chart potential corresponding to the project's actual flat potential. -/
lemma sphere_surfacePotential_pullback (k : ℕ) (z : ℂ) :
    spherePotential (surfacePotential k) (sphereChart z) =
      2 * ((k : ℝ) - 1) ^ 2 * ‖z‖ ^ (2 * k - 4) * (1 + ‖z‖ ^ 2) ^ 2 /
        (‖z‖ ^ (2 * k - 2) + 1) ^ 2 := by
  rw [spherePotential_pullback, stereoAreaDensity_eq]
  change (Surface.potV k z / (4 / (1 + ‖z‖ ^ 2) ^ 2)) = _
  unfold Surface.potV
  field_simp
  ring

end KsIndex.Spherical
