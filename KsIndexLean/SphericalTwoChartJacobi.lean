module

public import KsIndexLean.SphericalHemisphereMeasure

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Piecewise Jacobi density; global weak-domain matching is a separate condition. -/
def twoChartJacobiDensity (V : BoundedRealPotential) (uN uS vN vS : ComplexH1) : Sphere → ℂ := by
  classical
  exact (sphereChart '' (disk : Set ℂ)).piecewise
    (fun p => tangentPair (sphereWeakGradient uN p) (sphereWeakGradient vN p) -
      (spherePotential V p : ℂ) * (starRingEnd ℂ) (sphereWeakValue uN p) * sphereWeakValue vN p)
    (southJacobiDensity V uS vS)

lemma integrable_twoChartJacobiDensity (V : BoundedRealPotential) (uN uS vN vS : ComplexH1) :
    Integrable (twoChartJacobiDensity V uN uS vN vS) (volume : Measure Ambient).toSphere := by
  classical
  unfold twoChartJacobiDensity
  apply Integrable.piecewise
    (measurableEmbedding_sphereChart.measurableSet_image' disk.isOpen.measurableSet)
    (integrable_sphereJacobi_pair V uN vN)
  change Integrable _ ((volume : Measure Ambient).toSphere.restrict
    (sphereChart '' (disk : Set ℂ))ᶜ)
  rw [canonicalArea_lower_compl]
  exact integrable_southJacobiDensity V uS vS

/-- The sum of the two adopted chart forms is a single canonical whole-sphere integral. -/
theorem sum_weakJacobi_eq_sphere_integral (V : BoundedRealPotential) (uN uS vN vS : ComplexH1) :
    weakJacobi V uN vN + weakJacobi V uS vS =
      ∫ p, twoChartJacobiDensity V uN uS vN vS p ∂(volume : Measure Ambient).toSphere := by
  classical
  have hS : IntegrableOn (southJacobiDensity V uS vS)
      (sphereChart '' (disk : Set ℂ))ᶜ (volume : Measure Ambient).toSphere := by
    change Integrable _ ((volume : Measure Ambient).toSphere.restrict _)
    rw [canonicalArea_lower_compl]
    exact integrable_southJacobiDensity V uS vS
  rw [twoChartJacobiDensity,
    integral_piecewise
      (measurableEmbedding_sphereChart.measurableSet_image' disk.isOpen.measurableSet)
      (integrable_sphereJacobi_pair V uN vN) hS,
    canonicalArea_lower_compl,
    ← weakJacobi_eq_sphere_integral, ← weakJacobi_eq_south_integral]

end KsIndex.Spherical
