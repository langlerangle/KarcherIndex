module

public import KsIndexLean.PolarWeakAssembly

@[expose] public section


open Set MeasureTheory
open scoped ENNReal

namespace KsIndex.Trace

lemma enorm_sq_ofReal {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Real-valued exact Jacobian identity on the open radial interval. -/
theorem integral_annulus_eq_weighted_sliceLp {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    (∫ z in annulusSet a b, ‖u z‖ ^ 2) =
      ∫ t in Ioo a b, t * ‖sliceLp a b u t‖ ^ 2 := by
  have hF := aestronglyMeasurable_sliceLp ha hu
  have hp : ∀ᵐ t ∂volume.restrict (Ioo a b), 0 ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (lt_trans ha ht.1).le
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg ‖u z‖))
    (hu.aestronglyMeasurable.norm.pow 2),
    integral_eq_lintegral_of_nonneg_ae
      (hp.mono (fun t ht => mul_nonneg ht (sq_nonneg _)))
      (aestronglyMeasurable_id.mul (hF.norm.pow 2))]
  congr 1
  have h := lintegral_annulus_eq_weighted_sliceLp ha hu
  simp only [enorm_sq_ofReal] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [hp] with t ht
  rw [ENNReal.ofReal_mul ht]

/-- The actual L²-valued radial map has square-integrable norm. -/
theorem integrableOn_sliceLp_norm_sq {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun t => ‖sliceLp a b u t‖ ^ 2) (Ioo a b) volume := by
  have hfin : (∫⁻ z in annulusSet a b, ‖u z‖ₑ ^ (2 : ℕ)) < ∞ := by
    rw [lintegral_enorm_sq_eq _ hu.aestronglyMeasurable]
    exact ENNReal.pow_lt_top hu.eLpNorm_lt_top
  have hane : ENNReal.ofReal a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  have hbound := (le_lintegral_annulus ha hu).1
  have hsfin : (∫⁻ t in Ioo a b, ‖sliceLp a b u t‖ₑ ^ (2 : ℕ)) < ∞ := by
    calc _ = (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a *
        ∫⁻ t in Ioo a b, ‖sliceLp a b u t‖ₑ ^ (2 : ℕ)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hane ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (ENNReal.ofReal a)⁻¹ * ∫⁻ z in annulusSet a b, ‖u z‖ₑ ^ (2 : ℕ) :=
        mul_le_mul' le_rfl hbound
      _ < ∞ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr ha)) hfin
  refine ⟨(aestronglyMeasurable_sliceLp ha hu).norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun t => sq_nonneg _))).mpr
  simpa only [enorm_sq_ofReal] using hsfin

/-- Square integrability expressed as interval integrability on a nondegenerate radial interval. -/
theorem intervalIntegrable_sliceLp_norm_sq {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntervalIntegrable (fun t => ‖sliceLp a b u t‖ ^ 2) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr (integrableOn_sliceLp_norm_sq ha hu)

/-- Real-valued two-sided weight comparison, with finite integrals. -/
theorem integral_sliceLp_weight_bounds {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    a * (∫ t in Ioo a b, ‖sliceLp a b u t‖ ^ 2) ≤ ∫ z in annulusSet a b, ‖u z‖ ^ 2 ∧
    (∫ z in annulusSet a b, ‖u z‖ ^ 2) ≤ b * ∫ t in Ioo a b, ‖sliceLp a b u t‖ ^ 2 := by
  by_cases hab : a < b
  · have hs := integrableOn_sliceLp_norm_sq ha hu
    have ht : IntegrableOn (fun t => t * ‖sliceLp a b u t‖ ^ 2) (Ioo a b) volume := by
      have hbd : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖t‖ ≤ |a| + |b| := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [Real.norm_eq_abs, abs_of_pos (lt_trans ha ht.1)]
        exact ht.2.le.trans (le_trans (le_abs_self b) (le_add_of_nonneg_left (abs_nonneg a)))
      exact hs.bdd_smul (|a| + |b|) aestronglyMeasurable_id hbd
    rw [integral_annulus_eq_weighted_sliceLp ha hu, ← integral_const_mul, ← integral_const_mul]
    constructor
    · apply integral_mono_ae (hs.const_mul a) ht
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht'
      exact mul_le_mul_of_nonneg_right ht'.1.le (sq_nonneg _)
    · apply integral_mono_ae ht (hs.const_mul b)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht'
      exact mul_le_mul_of_nonneg_right ht'.2.le (sq_nonneg _)
  · have hI : Ioo a b = ∅ := Ioo_eq_empty hab
    have hA : annulusSet a b = ∅ := by
      ext z
      simp only [mem_annulusSet, mem_empty_iff_false, iff_false, not_and]
      exact fun hz => not_lt_of_ge ((not_lt.mp hab).trans hz.le)
    simp [hI, hA]

/-- The one-sided integrated radial-energy bound; no converse is asserted. -/
theorem radial_energy_bound {a b : ℝ} (ha : 0 < a) {U : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : MemLp (fun z => U z 1) 2 (volume.restrict (annulusSet a b)))
    (hI : MemLp (fun z => U z Complex.I) 2 (volume.restrict (annulusSet a b))) :
    a * (∫ t in Ioo a b, ‖sliceLp a b (radialField U) t‖ ^ 2) ≤
      2 * ∫ z in annulusSet a b, (‖U z 1‖ ^ 2 + ‖U z Complex.I‖ ^ 2) := by
  have hf := memLp_radialField ha h1 hI
  apply le_trans (integral_sliceLp_weight_bounds ha hf).1
  have hi1 := (memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).mp h1
  have hiI := (memLp_two_iff_integrable_sq_norm hI.aestronglyMeasurable).mp hI
  rw [← integral_const_mul]
  apply integral_mono_ae (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable |>.mp hf)
    ((hi1.add hiI).const_mul 2)
  filter_upwards [enorm_radialField_sq_le ha U] with z hz
  have hfinite : 2 * (‖U z 1‖ₑ ^ (2 : ℕ) + ‖U z Complex.I‖ₑ ^ (2 : ℕ)) ≠ ∞ := by
    finiteness
  have h := ENNReal.toReal_mono hfinite hz
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at h
  simpa using h

/-- Input-class invariance for the radial derivative, in the two applied directions. -/
theorem radial_sliceLp_congr_ae {a b : ℝ} (ha : 0 < a)
    {U V : ℂ → ℂ →L[ℝ] ℂ}
    (h1 : (fun z => U z 1) =ᵐ[volume.restrict (annulusSet a b)] (fun z => V z 1))
    (hI : (fun z => U z Complex.I) =ᵐ[volume.restrict (annulusSet a b)]
      (fun z => V z Complex.I)) :
    sliceLp a b (radialField U) =ᵐ[volume.restrict (Ioo a b)] sliceLp a b (radialField V) := by
  apply sliceLp_congr_ae ha
  filter_upwards [h1, hI] with z hz hz'
  simp only [radialField, hz, hz']

/-- The exact real Jacobian identity in interval-integral form. -/
theorem integral_annulus_eq_interval_weighted_sliceLp {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    (∫ z in annulusSet a b, ‖u z‖ ^ 2) =
      ∫ t in a..b, t * ‖sliceLp a b u t‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le hab.le,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b))]
  exact integral_annulus_eq_weighted_sliceLp ha hu

end KsIndex.Trace
