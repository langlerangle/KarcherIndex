module

public import KsIndexLean.SphericalWeakDirichlet
public import KsIndexLean.SphericalLpPullback

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- The carrier's tangent field in the actual sphere chart; only the disk image is used. -/
def sphereWeakGradient (u : ComplexH1) (p : Sphere) : Ambient × Ambient :=
  weakTangentGradient u (stereoCoord p.val)

lemma sphereWeakGradient_pullback (u : ComplexH1) (z : ℂ) :
    sphereWeakGradient u (sphereChart z) = weakTangentGradient u z := by
  simp [sphereWeakGradient, sphereChart, stereoCoord_stereoPoint]

/-- Exact equality with the adopted weak form, integrated against canonical sphere area. -/
theorem dirichlet_eq_sphere_integral (u v : ComplexH1) :
    dirichlet u v = ∫ p in sphereChart '' (disk : Set ℂ),
      tangentPair (sphereWeakGradient u p) (sphereWeakGradient v p)
        ∂(volume : Measure Ambient).toSphere := by
  rw [canonicalArea_restrict,
    Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.integral_map]
  simp only [sphereWeakGradient_pullback]
  rw [stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet]
  rw [integral_withDensity_eq_integral_toReal_smul
    continuous_stereoAreaDensity.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (stereoAreaDensity_pos _))]
  exact dirichlet_eq_tangent_chart u v

lemma integrable_sphereWeak_pair (u v : ComplexH1) :
    Integrable (fun p => tangentPair (sphereWeakGradient u p) (sphereWeakGradient v p))
      ((volume : Measure Ambient).toSphere.restrict (sphereChart '' (disk : Set ℂ))) := by
  rw [canonicalArea_restrict, Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.integrable_map_iff]
  simp only [Function.comp_def, sphereWeakGradient_pullback]
  rw [stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet,
    integrable_withDensity_iff_integrable_smul'
      continuous_stereoAreaDensity.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (stereoAreaDensity_pos _))]
  exact integrable_weakTangent_pair u v

end KsIndex.Spherical
