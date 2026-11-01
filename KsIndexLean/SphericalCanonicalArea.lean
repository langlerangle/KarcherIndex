module

public import KsIndexLean.SphericalSectorVolume

@[expose] public section


open Set MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
namespace KsIndex.Spherical

lemma measurable_sphere_pole : MeasurableSet {p : Sphere | p.val 2 = 1} := by
  apply isClosed_eq _ continuous_const |>.measurableSet
  fun_prop

lemma toSphere_pole_null :
    (volume : Measure Ambient).toSphere {p : Sphere | p.val 2 = 1} = 0 := by
  have hz : (volume : Measure (Fin 3 → ℝ)) {p | p 0 = 0} = 0 :=
    Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) 0 0
  have hv := volume_preserving_ambient_coordinates.quasiMeasurePreserving.preimage_null hz
  have hn : volume (Ioo (0 : ℝ) 1 •
      (Subtype.val '' {p : Sphere | p.val 2 = 1})) = 0 := by
    apply measure_mono_null _ hv
    rintro x ⟨r, hr, w, ⟨p, hp, rfl⟩, rfl⟩
    change r * p.val 0 = 0
    have h := sphere_sum_sq p
    have hp' : p.val 2 = 1 := hp
    have hx : p.val 0 = 0 := by nlinarith [sq_nonneg (p.val 1)]
    rw [hx, mul_zero]
  rw [Measure.toSphere_apply' _ measurable_sphere_pole, hn, mul_zero]

lemma sphereChart_image_preimage (A : Set Sphere) :
    sphereChart '' (sphereChart ⁻¹' A) = A \ {p : Sphere | p.val 2 = 1} := by
  rw [Set.image_preimage_eq_inter_range, range_sphereChart]
  rfl

/-- The compatible stereographic measure is the independent ambient-volume sphere measure. -/
theorem chartAreaMeasure_eq_toSphere :
    chartAreaMeasure = (volume : Measure Ambient).toSphere := by
  apply Measure.ext
  intro A hA
  have hs : MeasurableSet (sphereChart ⁻¹' A) := hA.preimage continuous_sphereChart.measurable
  have him : MeasurableSet (sphereChart '' (sphereChart ⁻¹' A)) := by
    rw [sphereChart_image_preimage]
    exact hA.diff measurable_sphere_pole
  have he : Subtype.val '' (sphereChart '' (sphereChart ⁻¹' A)) =
      stereoPoint '' (sphereChart ⁻¹' A) := by
    rw [Set.image_image]
    rfl
  have hv := (volume : Measure Ambient).toSphere_apply' him
  rw [he, volume_ambient_sector _ hs] at hv
  have hd : Module.finrank ℝ Ambient = 3 := by simp [Ambient]
  simp only [hd, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hv
  norm_num [← mul_assoc] at hv
  rw [ENNReal.mul_inv_cancel (by norm_num : (3 : ℝ≥0∞) ≠ 0)
    ENNReal.ofNat_ne_top, one_mul] at hv
  rw [sphereChart_image_preimage, measure_sdiff_null toSphere_pole_null] at hv
  rw [chartAreaMeasure, Measure.map_apply continuous_sphereChart.measurable hA]
  exact hv.symm

end KsIndex.Spherical
