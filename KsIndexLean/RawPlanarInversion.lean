module

public import KsIndexLean.PolarReconstructionEnergy

@[expose] public section


open Set MeasureTheory

noncomputable section
namespace KsIndex.Trace

/-- Radial inversion keeps the circle point fixed, unlike complex inversion. -/
def radialInversion (z : ℂ) : ℂ := (‖z‖ ^ 2)⁻¹ • z

lemma measurable_radialInversion : Measurable radialInversion :=
  (measurable_norm.pow_const 2).inv.smul measurable_id

lemma radialInversion_circle {r : ℝ} (hr : 0 < r) (w : Circle₁) :
    radialInversion (r • (w : ℂ)) = r⁻¹ • (w : ℂ) := by
  have hn : ‖(w : ℂ)‖ = 1 := by simp
  unfold radialInversion
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_of_pos hr, hn, mul_one]
  rw [smul_smul]
  congr 1
  field_simp

lemma sliceFun_radialInversion (u : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    sliceFun (fun z => u (radialInversion z)) r = sliceFun u r⁻¹ := by
  funext w
  exact congrArg u (radialInversion_circle hr w)

/-- The explicit inverted raw field has exactly the inverted circle profile a.e. -/
lemma ae_raw_inverted_slice {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1))) :
    ∀ᵐ r ∂volume.restrict (Ioo (1 : ℝ) 2),
      sliceFun (fun z => u (radialInversion z)) r =ᵐ[circleMeasure] sliceLp (1 / 2) 1 u r⁻¹ := by
  filter_upwards [ae_property_comp_inv_collar (ae_raw_sliceLp (by norm_num) hu),
    ae_restrict_mem measurableSet_Ioo] with r hr hrI
  rw [sliceFun_radialInversion u (by linarith [hrI.1])]
  exact hr

/-- Raw radial inversion preserves L² between these bounded collars. -/
theorem memLp_raw_radialInversion {u : ℂ → ℂ} (hm : Measurable u)
    (hu : MemLp u 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 1))) :
    MemLp (fun z => u (radialInversion z)) 2 (volume.restrict (annulusSet (1 : ℝ) 2)) := by
  apply memLp_annulus_of_raw_slices (by norm_num) (by norm_num)
    (hm.comp measurable_radialInversion)
    (comp_inv_integrable (intervalIntegrable_sliceLp_norm_sq (by norm_num) (by norm_num) hu))
  exact ae_raw_inverted_slice hu

end KsIndex.Trace
