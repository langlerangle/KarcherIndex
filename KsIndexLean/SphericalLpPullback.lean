module

public import KsIndexLean.SphericalCanonicalArea
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

lemma measurableEmbedding_sphereChart : MeasurableEmbedding sphereChart :=
  continuous_sphereChart.measurableEmbedding sphereChart_injective

lemma canonicalArea_restrict (A : Set Sphere) :
    (volume : Measure Ambient).toSphere.restrict A =
      Measure.map sphereChart (stereoAreaMeasure.restrict (sphereChart ⁻¹' A)) := by
  rw [← chartAreaMeasure_eq_toSphere, chartAreaMeasure]
  exact measurableEmbedding_sphereChart.restrict_map stereoAreaMeasure A

/-- Equality of actual Lp seminorms, including the L2 case. -/
theorem eLpNorm_sphere_pullback (F : Sphere → ℂ) (p : ℝ≥0∞) :
    eLpNorm F p (volume : Measure Ambient).toSphere =
      eLpNorm (F ∘ sphereChart) p stereoAreaMeasure := by
  rw [← chartAreaMeasure_eq_toSphere, chartAreaMeasure]
  exact measurableEmbedding_sphereChart.eLpNorm_map_measure

lemma memLp_sphere_pullback (F : Sphere → ℂ) (p : ℝ≥0∞) :
    MemLp F p (volume : Measure Ambient).toSphere ↔
      MemLp (F ∘ sphereChart) p stereoAreaMeasure := by
  rw [← chartAreaMeasure_eq_toSphere, chartAreaMeasure]
  exact measurableEmbedding_sphereChart.memLp_map_measure_iff

lemma eLpNorm_sphere_restrict (A : Set Sphere) (F : Sphere → ℂ) (p : ℝ≥0∞) :
    eLpNorm F p ((volume : Measure Ambient).toSphere.restrict A) =
      eLpNorm (F ∘ sphereChart) p (stereoAreaMeasure.restrict (sphereChart ⁻¹' A)) := by
  rw [canonicalArea_restrict]
  exact measurableEmbedding_sphereChart.eLpNorm_map_measure

lemma memLp_sphere_restrict (A : Set Sphere) (F : Sphere → ℂ) (p : ℝ≥0∞) :
    MemLp F p ((volume : Measure Ambient).toSphere.restrict A) ↔
      MemLp (F ∘ sphereChart) p (stereoAreaMeasure.restrict (sphereChart ⁻¹' A)) := by
  rw [canonicalArea_restrict]
  exact measurableEmbedding_sphereChart.memLp_map_measure_iff

end KsIndex.Spherical
