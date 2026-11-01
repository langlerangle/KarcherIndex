module

public import KsIndexLean.SphericalWeakJacobi
public import KsIndexLean.SphericalMeasureOverlap

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical

lemma reflectAmbient_inner (u v : Ambient) :
    inner ℝ (reflectAmbient u) (reflectAmbient v) = inner ℝ u v := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, reflectAmbient]

lemma tangentPair_reflect (U V : Ambient × Ambient) :
    tangentPair (reflectAmbient U.1, reflectAmbient U.2)
      (reflectAmbient V.1, reflectAmbient V.2) = tangentPair U V := by
  simp only [tangentPair, reflectAmbient_inner]

lemma measurableEmbedding_southChart : MeasurableEmbedding southChart := by
  apply (continuous_reflectSphere.comp continuous_sphereChart).measurableEmbedding
  exact reflectSphere_involutive.injective.comp sphereChart_injective

lemma canonicalArea_south_restrict (A : Set Sphere) :
    (volume : Measure Ambient).toSphere.restrict A =
      Measure.map southChart (stereoAreaMeasure.restrict (southChart ⁻¹' A)) := by
  rw [← chartAreaMeasure_eq_toSphere, ← map_southChart_stereoAreaMeasure]
  exact measurableEmbedding_southChart.restrict_map stereoAreaMeasure A

lemma south_integral_reflect (s : Set ℂ) (F : Sphere → ℂ) :
    ∫ p in southChart '' s, F (reflectSphere p) ∂(volume : Measure Ambient).toSphere =
      ∫ p in sphereChart '' s, F p ∂(volume : Measure Ambient).toSphere := by
  rw [canonicalArea_south_restrict, canonicalArea_restrict,
    Set.preimage_image_eq _ measurableEmbedding_southChart.injective,
    Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_southChart.integral_map, measurableEmbedding_sphereChart.integral_map]
  have h (p : Sphere) : reflectSphere (reflectSphere p) = p := reflectSphere_involutive p
  simp only [southChart, h]

lemma south_integrable_reflect (s : Set ℂ) (F : Sphere → ℂ) :
    Integrable (fun p => F (reflectSphere p))
      ((volume : Measure Ambient).toSphere.restrict (southChart '' s)) ↔
    Integrable F ((volume : Measure Ambient).toSphere.restrict (sphereChart '' s)) := by
  rw [canonicalArea_south_restrict, canonicalArea_restrict,
    Set.preimage_image_eq _ measurableEmbedding_southChart.injective,
    Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_southChart.integrable_map_iff,
    measurableEmbedding_sphereChart.integrable_map_iff]
  have h (p : Sphere) : reflectSphere (reflectSphere p) = p := reflectSphere_involutive p
  simp only [Function.comp_def, southChart, h]

end KsIndex.Spherical
