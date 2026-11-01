module

public import KsIndexLean.SphericalRadialVolume
public import KsIndexLean.SphericalChartMeasure

@[expose] public section


open Set MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
namespace KsIndex.Spherical

lemma lintegral_radial_weight_preimage (s : Set ℂ) (hs : MeasurableSet s)
    (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ p in radialCoord ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ s),
      ENNReal.ofReal (p 0 ^ 2) * h (radialCoord p).2 ∂volume =
      ENNReal.ofReal (1 / 3 : ℝ) * ∫⁻ z in s, h z ∂volume := by
  have hf : Measurable (fun p : ℝ × ℂ => ENNReal.ofReal (p.1 ^ 2) * h p.2) := by
    fun_prop
  have hc := volume_preserving_radialCoord.setLIntegral_comp_preimage
    ((measurableSet_Ioo (a := (0 : ℝ)) (b := 1)).prod hs) hf
  have he : (fun p : Fin 3 → ℝ => ENNReal.ofReal ((radialCoord p).1 ^ 2) *
      h (radialCoord p).2) = fun p => ENNReal.ofReal (p 0 ^ 2) * h (radialCoord p).2 := by
    funext p
    rw [radialCoord_apply]
  rw [he] at hc
  exact hc.trans (lintegral_radial_product s h hh)

/-- Cartesian volume of a unit radial sector over the actual stereographic chart. -/
theorem volume_cartesian_sector (s : Set ℂ) (hs : MeasurableSet s) :
    volume (Ioo (0 : ℝ) 1 • ((fun z => WithLp.ofLp (stereoPoint z)) '' s)) =
      ENNReal.ofReal (1 / 3 : ℝ) * stereoAreaMeasure s := by
  let t := radialCoord ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ s)
  have ht : MeasurableSet t := (measurableSet_Ioo.prod hs).preimage
    radialCoord.continuous.measurable
  have hp : t ⊆ {p | 0 < p 0} := by
    intro p hp
    have h := hp.1.1
    simpa [radialCoord_apply] using h
  have hj := lintegral_radialCartesian_image t ht hp (fun _ => 1)
  have hc := lintegral_radial_weight_preimage s hs
    (fun z => ENNReal.ofReal (stereoAreaDensity z))
    (ENNReal.continuous_ofReal.comp continuous_stereoAreaDensity).measurable
  rw [stereoAreaMeasure, withDensity_apply _ hs]
  rw [← hc, ← radialCartesian_image_sector]
  simpa only [t, lintegral_one, Measure.restrict_apply_univ, mul_one, stereoAreaDensity_eq,
    ENNReal.ofReal_mul (sq_nonneg _)] using hj

lemma ambient_sector_coordinates (s : Set ℂ) :
    WithLp.ofLp '' (Ioo (0 : ℝ) 1 • (stereoPoint '' s)) =
      Ioo (0 : ℝ) 1 • ((fun z => WithLp.ofLp (stereoPoint z)) '' s) := by
  ext x
  constructor
  · rintro ⟨p, ⟨r, hr, w, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨r, hr, WithLp.ofLp (stereoPoint z), ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨r, hr, w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨r • stereoPoint z, ⟨r, hr, stereoPoint z, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩

/-- The same sector formula for the canonical Euclidean ambient volume. -/
theorem volume_ambient_sector (s : Set ℂ) (hs : MeasurableSet s) :
    volume (Ioo (0 : ℝ) 1 • (stereoPoint '' s)) =
      ENNReal.ofReal (1 / 3 : ℝ) * stereoAreaMeasure s := by
  have he : MeasurableEmbedding (WithLp.ofLp : Ambient → (Fin 3 → ℝ)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toHomeomorph.measurableEmbedding
  have hm := volume_preserving_ambient_coordinates.setLIntegral_comp_emb he
    (fun _ => 1) (Ioo (0 : ℝ) 1 • (stereoPoint '' s))
  have hv : volume (Ioo (0 : ℝ) 1 • (stereoPoint '' s)) =
      volume (WithLp.ofLp '' (Ioo (0 : ℝ) 1 • (stereoPoint '' s))) := by
    simpa only [lintegral_one, Measure.restrict_apply_univ] using hm
  rw [hv, ambient_sector_coordinates, volume_cartesian_sector s hs]

end KsIndex.Spherical
