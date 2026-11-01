module

public import KsIndexLean.SphericalMassNorm

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

def zeroChartPotential : BoundedRealPotential where
  V := fun _ => 0
  C := 0
  nonneg := le_rfl
  measurable := aestronglyMeasurable_const
  bound := by filter_upwards with z; simp

lemma weakJacobi_zeroChartPotential (u v : ComplexH1) :
    weakJacobi zeroChartPotential u v = dirichlet u v := by
  rw [weakJacobi, potential_integral]
  simp [zeroChartPotential]

lemma joinedJacobiDensity_zeroChartPotential (uN uS vN vS : ComplexH1) (p : Sphere) :
    joinedJacobiDensity zeroChartPotential uN uS vN vS p =
      tangentPair (sphereJoinedGradient uN uS p) (sphereJoinedGradient vN vS p) := by
  simp [joinedJacobiDensity, sphereJoinedPotential, spherePotential, zeroChartPotential]

lemma integrable_joined_tangentPair (uN uS vN vS : ComplexH1) :
    Integrable (fun p => tangentPair (sphereJoinedGradient uN uS p)
      (sphereJoinedGradient vN vS p)) (volume : Measure Ambient).toSphere := by
  simpa only [funext (joinedJacobiDensity_zeroChartPotential uN uS vN vS)] using
    integrable_joinedJacobiDensity zeroChartPotential uN uS vN vS

theorem sum_dirichlet_eq_joined_integral (uN uS vN vS : ComplexH1) :
    dirichlet uN vN + dirichlet uS vS =
      ∫ p, tangentPair (sphereJoinedGradient uN uS p) (sphereJoinedGradient vN vS p)
        ∂(volume : Measure Ambient).toSphere := by
  have h := sum_weakJacobi_eq_joined_integral 0 zeroChartPotential uN uS vN vS
  simpa only [weakJacobi_zeroChartPotential, canonicalArea_restrict_slitSphere,
    funext (joinedJacobiDensity_zeroChartPotential uN uS vN vS)] using h

lemma tangentPair_self_re (U : Ambient × Ambient) :
    (tangentPair U U).re = ‖U.1‖ ^ 2 + ‖U.2‖ ^ 2 := by
  simp [tangentPair, -Complex.ofReal_pow]

/-- The actual canonical integral of the squared real and imaginary tangent gradients. -/
def sphereJoinedEnergy (u v : ComplexH1) : ℝ :=
  ∫ p, ‖(sphereJoinedGradient u v p).1‖ ^ 2 + ‖(sphereJoinedGradient u v p).2‖ ^ 2
    ∂(volume : Measure Ambient).toSphere

lemma integrable_joined_energy (u v : ComplexH1) :
    Integrable (fun p => ‖(sphereJoinedGradient u v p).1‖ ^ 2 +
      ‖(sphereJoinedGradient u v p).2‖ ^ 2) (volume : Measure Ambient).toSphere := by
  have h := (integrable_joined_tangentPair u v u v).re
  change Integrable (fun p => (tangentPair (sphereJoinedGradient u v p)
    (sphereJoinedGradient u v p)).re) (volume : Measure Ambient).toSphere at h
  simpa only [tangentPair_self_re] using h

lemma sphereJoinedEnergy_eq (u v : ComplexH1) :
    sphereJoinedEnergy u v = ‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2 +
      (‖dxLp v‖ ^ 2 + ‖dyLp v‖ ^ 2) := by
  have h := integral_re (integrable_joined_tangentPair u v u v)
  have he := sum_dirichlet_eq_joined_integral u v u v
  rw [← he] at h
  change (∫ p, (tangentPair (sphereJoinedGradient u v p)
    (sphereJoinedGradient u v p)).re ∂(volume : Measure Ambient).toSphere) =
    (dirichlet u u + dirichlet v v).re at h
  have hd (x : ComplexH1) : (dirichlet x x).re = ‖dxLp x‖ ^ 2 + ‖dyLp x‖ ^ 2 := by
    simp only [dirichlet, inner_self_eq_norm_sq_to_K]
    change ((‖dxLp x‖ : ℂ) ^ 2 + (‖dyLp x‖ : ℂ) ^ 2).re = _
    simp [pow_two]
  simpa only [sphereJoinedEnergy, tangentPair_self_re, Complex.add_re, hd] using h

end KsIndex.Spherical
