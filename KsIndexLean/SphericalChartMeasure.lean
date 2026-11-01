module

public import KsIndexLean.SphericalMetric
public import KsIndexLean.SphericalChartHomeomorph
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

lemma continuous_stereoAreaDensity : Continuous stereoAreaDensity := by
  simp only [funext stereoAreaDensity_eq]
  apply Continuous.div continuous_const (by fun_prop)
  intro z
  positivity

lemma stereoAreaDensity_pos (z : ℂ) : 0 < stereoAreaDensity z := by
  rw [stereoAreaDensity_eq]
  positivity

/-- Planar measure weighted by the proved Gram area density. -/
def stereoAreaMeasure : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (stereoAreaDensity z))

/-- Measure on the actual sphere induced by the Gram-density chart.
Identification with an independently defined surface-area measure is separate. -/
def chartAreaMeasure : Measure Sphere := Measure.map sphereChart stereoAreaMeasure

theorem lintegral_chartAreaMeasure (F : Sphere → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p, F p ∂chartAreaMeasure =
      ∫⁻ z, ENNReal.ofReal (4 / (1 + ‖z‖ ^ 2) ^ 2) * F (sphereChart z) ∂volume := by
  rw [chartAreaMeasure, lintegral_map hF continuous_sphereChart.measurable]
  rw [stereoAreaMeasure]
  simpa only [Pi.mul_apply, Function.comp_apply, stereoAreaDensity_eq] using
    lintegral_withDensity_eq_lintegral_mul volume
      (continuous_stereoAreaDensity.measurable.ennreal_ofReal)
      (hF.comp continuous_sphereChart.measurable)

lemma chartAreaMeasure_singleton (p : Sphere) : chartAreaMeasure {p} = 0 := by
  rw [chartAreaMeasure, Measure.map_apply continuous_sphereChart.measurable
    (measurableSet_singleton p)]
  by_cases h : ∃ z, sphereChart z = p
  · obtain ⟨z, rfl⟩ := h
    have he : sphereChart ⁻¹' {sphereChart z} = {z} := by
      ext w
      simp only [mem_preimage, mem_singleton_iff, sphereChart_injective.eq_iff]
    rw [he, stereoAreaMeasure, withDensity_apply _ (measurableSet_singleton z)]
    simp
  · have he : sphereChart ⁻¹' {p} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact h ⟨z, hz⟩
    rw [he, measure_empty]

theorem integral_chartAreaMeasure (F : Sphere → ℂ)
    (hF : AEStronglyMeasurable F chartAreaMeasure) :
    ∫ p, F p ∂chartAreaMeasure =
      ∫ z, (4 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) • F (sphereChart z) ∂volume := by
  rw [chartAreaMeasure, integral_map continuous_sphereChart.measurable.aemeasurable hF]
  rw [stereoAreaMeasure]
  have hfin : ∀ᵐ z ∂(volume : Measure ℂ),
      ENNReal.ofReal (stereoAreaDensity z) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [integral_withDensity_eq_integral_toReal_smul
    continuous_stereoAreaDensity.measurable.ennreal_ofReal hfin]
  congr 1
  funext z
  rw [ENNReal.toReal_ofReal (le_of_lt (stereoAreaDensity_pos z)), stereoAreaDensity_eq]

end KsIndex.Spherical
