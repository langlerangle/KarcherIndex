module

public import KsIndexLean.SphericalDiskMeasureBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1 KsIndex.Trace

lemma memL2_sphereWeakValue_disk (u : ComplexH1) :
    MemLp (sphereWeakValue u) 2 ((volume : Measure Ambient).toSphere.restrict
      (sphereChart '' (disk : Set ℂ))) := by
  rw [canonicalArea_restrict, Set.preimage_image_eq _ sphereChart_injective,
    measurableEmbedding_sphereChart.memLp_map_measure_iff]
  simpa only [Function.comp_def, sphereWeakValue_pullback] using
    (memLp_stereoAreaMeasure_disk_iff (valueCLM u) 2).mpr (Lp.memLp (valueCLM u))

lemma memL2_southWeakValue_disk (u : ComplexH1) :
    MemLp (fun p => sphereWeakValue u (reflectSphere p)) 2
      ((volume : Measure Ambient).toSphere.restrict (southChart '' (disk : Set ℂ))) := by
  rw [canonicalArea_south_restrict,
    Set.preimage_image_eq _ measurableEmbedding_southChart.injective,
    measurableEmbedding_southChart.memLp_map_measure_iff]
  have hi (p : Sphere) : reflectSphere (reflectSphere p) = p := reflectSphere_involutive p
  simpa only [Function.comp_def, southChart, hi, sphereWeakValue_pullback] using
    (memLp_stereoAreaMeasure_disk_iff (valueCLM u) 2).mpr (Lp.memLp (valueCLM u))

/-- Independent disk data always give an L2 sphere value; weak H1 gluing needs trace matching. -/
lemma memL2_sphereJoinedValue (u v : ComplexH1) :
    MemLp (sphereJoinedValue u v) 2 (volume : Measure Ambient).toSphere := by
  classical
  have hs : MemLp (fun p => sphereWeakValue v (reflectSphere p)) 2
      ((volume : Measure Ambient).toSphere.restrict (sphereChart '' (disk : Set ℂ))ᶜ) := by
    rw [canonicalArea_lower_compl]
    exact memL2_southWeakValue_disk v
  have h := (memL2_sphereWeakValue_disk u).piecewise
    (measurableEmbedding_sphereChart.measurableSet_image' disk.isOpen.measurableSet) hs
  apply h.ae_eq
  have he : ∀ᵐ p ∂(volume : Measure Ambient).toSphere, p.val 2 ≠ 0 := by
    simpa only [ae_iff, not_not] using sphere_equator_null
  filter_upwards [he] with p hp
  by_cases hn : p.val 2 < 0
  · have hm : p ∈ sphereChart '' (disk : Set ℂ) := by rw [sphereChart_disk_eq_lower]; exact hn
    simp [sphereJoinedValue, sphereWeakValue, hm, hn.le]
  · have hpos : 0 < p.val 2 := lt_of_le_of_ne (le_of_not_gt hn) hp.symm
    have hm : p ∉ sphereChart '' (disk : Set ℂ) := by rw [sphereChart_disk_eq_lower]; exact hn
    simp [sphereJoinedValue, sphereWeakValue, hm, not_le.mpr hpos]

lemma memL2_sphereChartFunction {A : Set Circle₁} (hA : IsOpen A)
    (F : SphereChartFunctions A hA) : MemLp F.val 2 (volume : Measure Ambient).toSphere := by
  obtain ⟨u, v, ht, hn, hs⟩ := sphere_chart_reconstruction hA F.val F.property.1 F.property.2
  exact (memL2_sphereJoinedValue u v).ae_eq ((sphere_ae_eq_iff_north _ _).mpr hn)

lemma sphereChartL2_lt_top {A : Set Circle₁} (hA : IsOpen A) (q : SphereChartSpace A hA) :
    sphereChartL2 hA q < ∞ := by
  induction q using Quotient.inductionOn with
  | h F => exact (memL2_sphereChartFunction hA F).eLpNorm_lt_top

end KsIndex.Spherical
