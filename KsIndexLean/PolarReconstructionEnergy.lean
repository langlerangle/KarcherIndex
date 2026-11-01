module

public import KsIndexLean.DiskCutoffGluing

@[expose] public section


open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace KsIndex.Trace

lemma lintegral_circle_Lp_sq (F : Lp ℂ 2 circleMeasure) :
    (∫⁻ w, ‖F w‖ₑ ^ (2 : ℕ) ∂circleMeasure) = ‖F‖ₑ ^ (2 : ℕ) := by
  rw [Lp.enorm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.aestronglyMeasurable F)]
  have ht : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [ht, ← ENNReal.rpow_natCast
    ((∫⁻ w, ‖F w‖ₑ ^ (((2 : ℕ) : ℝ)) ∂circleMeasure) ^ (1 / ((2 : ℕ) : ℝ))) 2,
    ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_natCast]

/-- Reverse polar L² control starts from supplied raw slices, before constructing sliceLp. -/
theorem memLp_annulus_of_raw_slices {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : ℂ → ℂ} (hu : Measurable u) {F : ℝ → Lp ℂ 2 circleMeasure}
    (hF : IntervalIntegrable (fun r => ‖F r‖ ^ 2) volume a b)
    (hs : ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun u r =ᵐ[circleMeasure] F r) :
    MemLp u 2 (volume.restrict (annulusSet a b)) := by
  have hfin : (∫⁻ r in Ioo a b, ‖F r‖ₑ ^ (2 : ℕ)) < ∞ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le] at hF
    have h := (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun r => sq_nonneg ‖F r‖)).mp hF.hasFiniteIntegral
    simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
  have he : (∫⁻ r in Ioo a b, ∫⁻ w, ‖sliceFun u r w‖ₑ ^ (2 : ℕ) ∂circleMeasure) =
      ∫⁻ r in Ioo a b, ‖F r‖ₑ ^ (2 : ℕ) := by
    apply lintegral_congr_ae
    filter_upwards [hs] with r hr
    rw [← lintegral_circle_Lp_sq]
    exact lintegral_congr_ae (hr.fun_comp (fun z : ℂ => ‖z‖ₑ ^ (2 : ℕ)))
  have hmeas : Measurable (fun r =>
      ∫⁻ w, ‖sliceFun u r w‖ₑ ^ (2 : ℕ) ∂circleMeasure) :=
    measurable_slice_lintegral (hu.enorm.pow_const 2)
  have hbound : (∫⁻ z in annulusSet a b, ‖u z‖ₑ ^ (2 : ℕ)) ≤
      ENNReal.ofReal b * ∫⁻ r in Ioo a b,
        ∫⁻ w, ‖sliceFun u r w‖ₑ ^ (2 : ℕ) ∂circleMeasure := by
    rw [lintegral_annulus_sq ha hu, ← lintegral_const_mul _ hmeas]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hr.2.le) le_rfl
  rw [memLp_iff]
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hu.aestronglyMeasurable).mpr
  have h := hbound.trans_lt (by rw [he]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  simpa [ENNReal.rpow_natCast] using h

lemma sliceLp_eq_of_raw_ae {a b r : ℝ} (hr : r ∈ Ioo a b) {u : ℂ → ℂ}
    (F : Lp ℂ 2 circleMeasure) (he : sliceFun u r =ᵐ[circleMeasure] F) :
    sliceLp a b u r = F := by
  have hm := (Lp.memLp F).ae_eq he.symm
  rw [sliceLp_of_memLp hr hm]
  exact Lp.ext (hm.coeFn_toLp.trans he)

lemma ae_raw_sliceLp {a b : ℝ} (ha : 0 < a) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    ∀ᵐ r ∂volume.restrict (Ioo a b), sliceFun u r =ᵐ[circleMeasure] sliceLp a b u r := by
  filter_upwards [ae_sliceFun_memLp ha hu, ae_restrict_mem measurableSet_Ioo] with r hm hr
  rw [sliceLp_of_memLp hr hm]
  exact hm.coeFn_toLp.symm

end KsIndex.Trace
