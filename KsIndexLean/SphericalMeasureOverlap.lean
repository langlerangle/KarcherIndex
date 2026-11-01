module

public import KsIndexLean.SphericalInversionMeasure
public import KsIndexLean.SphericalChartTransition

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical

lemma stereoAreaMeasure_ae_ne_zero : ∀ᵐ z ∂stereoAreaMeasure, z ≠ 0 := by
  simp only [ae_iff, not_not]
  change stereoAreaMeasure {0} = 0
  rw [stereoAreaMeasure, withDensity_apply _ (measurableSet_singleton (0 : ℂ))]
  simp

/-- The complementary chart with the same Gram density gives exactly the same measure. -/
theorem map_southChart_stereoAreaMeasure :
    Measure.map southChart stereoAreaMeasure = chartAreaMeasure := by
  have he : southChart =ᵐ[stereoAreaMeasure] sphereChart ∘ Bracket.σ := by
    filter_upwards [stereoAreaMeasure_ae_ne_zero] with z hz
    exact southChart_eq_sigma hz
  rw [Measure.map_congr he, ← Measure.map_map continuous_sphereChart.measurable measurable_sigma,
    map_stereoAreaMeasure_sigma]
  rfl

end KsIndex.Spherical
