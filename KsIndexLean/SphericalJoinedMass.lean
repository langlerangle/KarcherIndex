module

public import KsIndexLean.SphericalJoinedL2

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

lemma sphereJoinedValue_lower (u v : ComplexH1) {p : Sphere}
    (hp : p ∈ sphereChart '' (disk : Set ℂ)) : sphereJoinedValue u v p = sphereWeakValue u p := by
  have h : p.val 2 < 0 := by rwa [sphereChart_disk_eq_lower] at hp
  simp [sphereJoinedValue, sphereWeakValue, h.le]

lemma sphereJoinedValue_upper (u v : ComplexH1) {p : Sphere}
    (hp : p ∈ southChart '' (disk : Set ℂ)) :
    sphereJoinedValue u v p = sphereWeakValue v (reflectSphere p) := by
  have h : 0 < p.val 2 := by rwa [southChart_disk_eq_upper] at hp
  simp [sphereJoinedValue, sphereWeakValue, not_le.mpr h]

/-- Exact canonical squared mass, retaining extended integrals. -/
theorem sphereJoinedValue_mass_split (u v : ComplexH1) :
    (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2) ∂(volume : Measure Ambient).toSphere) =
      (∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖valueCLM u z‖ ^ 2) ∂stereoAreaMeasure) +
      ∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖valueCLM v z‖ ^ 2) ∂stereoAreaMeasure := by
  rw [← lintegral_add_compl _
    (measurableEmbedding_sphereChart.measurableSet_image' disk.isOpen.measurableSet),
    canonicalArea_lower_compl]
  congr 1
  · rw [canonicalArea_restrict, Set.preimage_image_eq _ sphereChart_injective,
      measurableEmbedding_sphereChart.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    rw [sphereJoinedValue_lower u v ⟨z, hz, rfl⟩, sphereWeakValue_pullback]
  · rw [canonicalArea_south_restrict,
      Set.preimage_image_eq _ measurableEmbedding_southChart.injective,
      measurableEmbedding_southChart.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem disk.isOpen.measurableSet] with z hz
    rw [sphereJoinedValue_upper u v ⟨z, hz, rfl⟩]
    change ENNReal.ofReal
      (‖sphereWeakValue v (reflectSphere (reflectSphere (sphereChart z)))‖ ^ 2) = _
    rw [reflectSphere_involutive (sphereChart z), sphereWeakValue_pullback]

lemma disk_mass_comparison (f : ℂ → ℂ) :
    (∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖f z‖ ^ 2)) ≤
      (∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖f z‖ ^ 2) ∂stereoAreaMeasure) ∧
    (∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖f z‖ ^ 2) ∂stereoAreaMeasure) ≤
      4 * ∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖f z‖ ^ 2) := by
  refine ⟨lintegral_mono' volume_disk_le_stereoAreaMeasure le_rfl, ?_⟩
  have h := lintegral_mono' stereoAreaMeasure_disk_le
    (le_refl (fun z => ENNReal.ofReal (‖f z‖ ^ 2)))
  simpa only [lintegral_smul_measure, smul_eq_mul] using h

theorem sphereJoinedValue_mass_comparison (u v : ComplexH1) :
    ((∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖valueCLM u z‖ ^ 2)) +
      ∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖valueCLM v z‖ ^ 2)) ≤
      (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2) ∂(volume : Measure Ambient).toSphere) ∧
    (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2) ∂(volume : Measure Ambient).toSphere) ≤
      4 * ((∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖valueCLM u z‖ ^ 2)) +
        ∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖valueCLM v z‖ ^ 2)) := by
  rw [sphereJoinedValue_mass_split, mul_add]
  exact ⟨add_le_add (disk_mass_comparison _).1 (disk_mass_comparison _).1,
    add_le_add (disk_mass_comparison _).2 (disk_mass_comparison _).2⟩

end KsIndex.Spherical
