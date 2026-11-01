module

public import KsIndexLean.DiskAngularProjection

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma continuous_eq_zero_at_zero_of_fourierCoeffOn (f : ℝ → ℂ) (hf : Continuous f)
    (hz : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos f n = 0) : f 0 = 0 := by
  have hi : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume 0 (2 * Real.pi) :=
    (hf.norm.pow 2).intervalIntegrable _ _
  have hm : MemLp f 2 (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr hi.1
  have hs := tsum_sq_fourierCoeffOn Real.two_pi_pos hm
  simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    tsum_zero, sub_zero, smul_eq_mul] at hs
  have hint : (∫ x in (0 : ℝ)..2 * Real.pi, ‖f x‖ ^ 2) = 0 :=
    (mul_eq_zero.mp hs.symm).resolve_left (inv_ne_zero Real.two_pi_pos.ne')
  have ha := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    Real.two_pi_pos.le (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖)) hi).mp hint
  have hf0 : f =ᵐ[volume.restrict (Ioc 0 (2 * Real.pi))] 0 := by
    filter_upwards [ha] with x hx
    apply norm_eq_zero.mp
    change ‖f x‖ ^ 2 = 0 at hx
    nlinarith [norm_nonneg (f x)]
  have hcc : f =ᵐ[volume.restrict (Icc 0 (2 * Real.pi))] 0 := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hf0
  exact MeasureTheory.Measure.eqOn_Icc_of_ae_eq volume Real.two_pi_pos.ne hcc hf.continuousOn continuousOn_const
    ⟨le_rfl, Real.two_pi_pos.le⟩

/-- A continuous functional vanishing on finite-trace tests vanishes on the
whole weak H1 carrier. This is the Fourier separation step for density. -/
theorem finiteFourierTraceTests_annihilator (L : ComplexH1 →L[ℂ] ℂ)
    (hL : ∀ v ∈ finiteFourierTraceTests, L v = 0) (u : ComplexH1) : L u = 0 := by
  have h := continuous_eq_zero_at_zero_of_fourierCoeffOn
    (fun θ => L (diskRotation θ u)) (L.continuous.comp (continuous_diskRotation u))
    (fun n => (diskAngularProjection_map L n u).symm.trans
      (hL _ (diskAngularProjection_mem_finiteFourierTraceTests n u)))
  simpa only [diskRotation_zero] using h

end KsIndex.Trace
