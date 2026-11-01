module

public import KsIndexLean.SphericalWeakDirichletIntegral

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

/-- Weak carrier values on its spherical disk chart; no use outside that chart is asserted. -/
def sphereWeakValue (u : ComplexH1) (p : Sphere) : ℂ := valueCLM u (stereoCoord p.val)

/-- The spherical potential whose area-weighted pullback is the adopted flat potential. -/
def spherePotential (V : BoundedRealPotential) (p : Sphere) : ℝ :=
  V.V (stereoCoord p.val) / stereoAreaDensity (stereoCoord p.val)

lemma sphereWeakValue_pullback (u : ComplexH1) (z : ℂ) :
    sphereWeakValue u (sphereChart z) = valueCLM u z := by
  simp [sphereWeakValue, sphereChart, stereoCoord_stereoPoint]

lemma spherePotential_pullback (V : BoundedRealPotential) (z : ℂ) :
    spherePotential V (sphereChart z) = V.V z / stereoAreaDensity z := by
  simp [spherePotential, sphereChart, stereoCoord_stereoPoint]

lemma spherePotential_pair_cancel (V : BoundedRealPotential) (u v : ComplexH1) (z : ℂ) :
    (stereoAreaDensity z : ℂ) * ((spherePotential V (sphereChart z) : ℂ) *
      (starRingEnd ℂ) (sphereWeakValue u (sphereChart z)) *
        sphereWeakValue v (sphereChart z)) =
      (V.V z : ℂ) * (starRingEnd ℂ) (valueCLM u z) * valueCLM v z := by
  have hd : (stereoAreaDensity z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (stereoAreaDensity_pos z))
  rw [spherePotential_pullback, sphereWeakValue_pullback, sphereWeakValue_pullback,
    Complex.ofReal_div]
  field_simp

lemma potential_eq_sphere_integral (V : BoundedRealPotential) (u v : ComplexH1) :
    potential V u v = ∫ p in sphereChart '' (disk : Set ℂ),
      (spherePotential V p : ℂ) * (starRingEnd ℂ) (sphereWeakValue u p) *
        sphereWeakValue v p ∂(volume : Measure Ambient).toSphere := by
  rw [canonicalArea_restrict, Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.integral_map,
    stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet,
    integral_withDensity_eq_integral_toReal_smul
      continuous_stereoAreaDensity.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (le_of_lt (stereoAreaDensity_pos _))]
  rw [potential_integral]
  apply integral_congr_ae
  filter_upwards with z
  exact (spherePotential_pair_cancel V u v z).symm

lemma integrable_spherePotential_pair (V : BoundedRealPotential) (u v : ComplexH1) :
    Integrable (fun p => (spherePotential V p : ℂ) *
      (starRingEnd ℂ) (sphereWeakValue u p) * sphereWeakValue v p)
      ((volume : Measure Ambient).toSphere.restrict (sphereChart '' (disk : Set ℂ))) := by
  rw [canonicalArea_restrict, Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.integrable_map_iff,
    stereoAreaMeasure, restrict_withDensity disk.isOpen.measurableSet,
    integrable_withDensity_iff_integrable_smul'
      continuous_stereoAreaDensity.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [Function.comp_def, ENNReal.toReal_ofReal (le_of_lt (stereoAreaDensity_pos _))]
  apply (potential_integrable V u v).congr
  filter_upwards with z
  exact (spherePotential_pair_cancel V u v z).symm

end KsIndex.Spherical
