module

public import KsIndexLean.SphericalSouthTransport

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Tangent vectors are reflected together with the base point in the south chart. -/
def southWeakGradient (u : ComplexH1) (p : Sphere) : Ambient × Ambient :=
  (reflectAmbient (sphereWeakGradient u (reflectSphere p)).1,
    reflectAmbient (sphereWeakGradient u (reflectSphere p)).2)

lemma southWeakGradient_pullback (u : ComplexH1) (z : ℂ) :
    southWeakGradient u (southChart z) =
      (reflectAmbient (weakTangentGradient u z).1,
        reflectAmbient (weakTangentGradient u z).2) := by
  unfold southWeakGradient southChart
  rw [reflectSphere_involutive (sphereChart z), sphereWeakGradient_pullback]

/-- The same weak Jacobi density in the actual complementary chart. -/
def southJacobiDensity (V : BoundedRealPotential) (u v : ComplexH1) (p : Sphere) : ℂ :=
  tangentPair (southWeakGradient u p) (southWeakGradient v p) -
    (spherePotential V (reflectSphere p) : ℂ) *
      (starRingEnd ℂ) (sphereWeakValue u (reflectSphere p)) *
        sphereWeakValue v (reflectSphere p)

lemma southJacobiDensity_reflect (V : BoundedRealPotential) (u v : ComplexH1) (p : Sphere) :
    southJacobiDensity V u v p =
      tangentPair (sphereWeakGradient u (reflectSphere p))
        (sphereWeakGradient v (reflectSphere p)) -
          (spherePotential V (reflectSphere p) : ℂ) *
            (starRingEnd ℂ) (sphereWeakValue u (reflectSphere p)) *
              sphereWeakValue v (reflectSphere p) := by
  simp only [southJacobiDensity, southWeakGradient, tangentPair_reflect]

lemma integrable_southJacobiDensity (V : BoundedRealPotential) (u v : ComplexH1) :
    Integrable (southJacobiDensity V u v)
      ((volume : Measure Ambient).toSphere.restrict (southChart '' (disk : Set ℂ))) := by
  have h := (south_integrable_reflect (disk : Set ℂ) _).mpr
    (integrable_sphereJacobi_pair V u v)
  simpa only [funext (southJacobiDensity_reflect V u v)] using h

theorem weakJacobi_eq_south_integral (V : BoundedRealPotential) (u v : ComplexH1) :
    weakJacobi V u v = ∫ p in southChart '' (disk : Set ℂ),
      southJacobiDensity V u v p ∂(volume : Measure Ambient).toSphere := by
  rw [weakJacobi_eq_sphere_integral]
  simpa only [funext (southJacobiDensity_reflect V u v)] using
    (south_integral_reflect (disk : Set ℂ) (fun p =>
      tangentPair (sphereWeakGradient u p) (sphereWeakGradient v p) -
        (spherePotential V p : ℂ) * (starRingEnd ℂ) (sphereWeakValue u p) *
          sphereWeakValue v p)).symm

end KsIndex.Spherical
