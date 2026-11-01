module

public import KsIndexLean.SphericalLpPullback

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical

lemma setLIntegral_sphere_weight (A : Set Sphere) (hA : MeasurableSet A)
    (F : Sphere → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p in A, F p ∂(volume : Measure Ambient).toSphere =
      ∫⁻ z in sphereChart ⁻¹' A,
        ENNReal.ofReal (4 / (1 + ‖z‖ ^ 2) ^ 2) * F (sphereChart z) ∂volume := by
  rw [← lintegral_indicator hA, ← chartAreaMeasure_eq_toSphere,
    lintegral_chartAreaMeasure _ (hF.indicator hA),
    ← lintegral_indicator (hA.preimage continuous_sphereChart.measurable)]
  congr 1
  funext z
  by_cases hz : sphereChart z ∈ A <;> simp [hz]

lemma setIntegral_sphere_weight (A : Set Sphere) (hA : MeasurableSet A)
    (F : Sphere → ℂ) (hF : Measurable F) :
    ∫ p in A, F p ∂(volume : Measure Ambient).toSphere =
      ∫ z in sphereChart ⁻¹' A,
        (4 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) • F (sphereChart z) ∂volume := by
  rw [← integral_indicator hA, ← chartAreaMeasure_eq_toSphere,
    integral_chartAreaMeasure _ (hF.indicator hA).aestronglyMeasurable,
    ← integral_indicator (hA.preimage continuous_sphereChart.measurable)]
  congr 1
  funext z
  by_cases hz : sphereChart z ∈ A <;> simp [hz]

/-- Squared L2 mass, expressed without hiding possible divergence in a real integral. -/
lemma lintegral_sphere_norm_sq (A : Set Sphere) (hA : MeasurableSet A)
    (F : Sphere → ℂ) (hF : Measurable F) :
    ∫⁻ p in A, ENNReal.ofReal (‖F p‖ ^ 2) ∂(volume : Measure Ambient).toSphere =
      ∫⁻ z in sphereChart ⁻¹' A, ENNReal.ofReal (4 / (1 + ‖z‖ ^ 2) ^ 2) *
        ENNReal.ofReal (‖F (sphereChart z)‖ ^ 2) ∂volume := by
  exact setLIntegral_sphere_weight A hA _ (by fun_prop)

/-- Hermitian convention: conjugate-linear in the first argument. -/
lemma integral_sphere_pairing (A : Set Sphere) (hA : MeasurableSet A)
    (F G : Sphere → ℂ) (hF : Measurable F) (hG : Measurable G) :
    ∫ p in A, (starRingEnd ℂ) (F p) * G p ∂(volume : Measure Ambient).toSphere =
      ∫ z in sphereChart ⁻¹' A, (4 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) •
        ((starRingEnd ℂ) (F (sphereChart z)) * G (sphereChart z)) ∂volume := by
  exact setIntegral_sphere_weight A hA _ (by fun_prop)

lemma integrable_sphere_pairing (A : Set Sphere) (F G : Sphere → ℂ)
    (hF : MemLp F 2 ((volume : Measure Ambient).toSphere.restrict A))
    (hG : MemLp G 2 ((volume : Measure Ambient).toSphere.restrict A)) :
    Integrable (fun p => (starRingEnd ℂ) (F p) * G p)
      ((volume : Measure Ambient).toSphere.restrict A) := by
  exact hF.star.integrable_mul hG

end KsIndex.Spherical
