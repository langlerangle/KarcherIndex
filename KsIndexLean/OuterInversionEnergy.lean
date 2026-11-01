module

public import KsIndexLean.DiskExtensionL2

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- Squared L2 energy of an inverted disk function on the outer annulus. -/
lemma integral_sq_sigma_outer_le (f : L2C) :
    (∫ z in annulusSet (1 : ℝ) 2, ‖f (σ z)‖ ^ 2) ≤ 16 * ‖f‖ ^ 2 := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal (‖f z‖ ^ 2)) :=
    ((Lp.stronglyMeasurable f).measurable.norm.pow_const 2).ennreal_ofReal
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have ho := memLp_sigma_outer (Lp.memLp f)
  have hoi := (memLp_two_iff_integrable_sq_norm ho.aestronglyMeasurable).mp ho
  simp only [Function.comp_apply] at hoi
  have h := lintegral_sigma_outer_le _ hm
  have ht : (16 * ∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖f z‖ ^ 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by
      simpa only [Real.enorm_eq_ofReal (sq_nonneg (_ : ℝ))] using hi.hasFiniteIntegral.ne)
  have hr := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_mul] at hr
  rw [lp_norm_sq]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hoi.1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hi.1]
  simpa using hr

lemma diskExtension_outer_energy_le (u : ComplexH1) (d : ℂ) :
    (∫ z in annulusSet (1 : ℝ) 2, ‖diskExtensionJet u z d‖ ^ 2) ≤
      512 * ‖d‖ ^ 2 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) := by
  have hm := (diskExtension_direction_memLp u d).mono_measure
    (Measure.restrict_mono (show annulusSet (1 : ℝ) 2 ⊆ Metric.ball 0 2 from
      fun z hz => by simpa only [Metric.mem_ball, dist_zero_right] using hz.2) le_rfl)
  have hj := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hx := memLp_sigma_outer (Lp.memLp (dxLp u))
  have hy := memLp_sigma_outer (Lp.memLp (dyLp u))
  have hxi := (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  have hyi := (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy
  simp only [Function.comp_apply] at hxi hyi
  have hbound : (∫ z in annulusSet (1 : ℝ) 2, ‖diskExtensionJet u z d‖ ^ 2) ≤
      ∫ z in annulusSet (1 : ℝ) 2,
        (32 * ‖d‖ ^ 2) * (‖dxLp u (σ z)‖ ^ 2 + ‖dyLp u (σ z)‖ ^ 2) := by
    apply integral_mono_ae hj ((hxi.add hyi).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
    have hb := diskExtensionJet_outer_bound u d hz
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
    have ha : (‖dxLp u (σ z)‖ + ‖dyLp u (σ z)‖) ^ 2 ≤
        2 * (‖dxLp u (σ z)‖ ^ 2 + ‖dyLp u (σ z)‖ ^ 2) := by
      nlinarith [sq_nonneg (‖dxLp u (σ z)‖ - ‖dyLp u (σ z)‖)]
    have hh := mul_le_mul_of_nonneg_left ha (sq_nonneg (4 * ‖d‖))
    simp only [Pi.add_apply]
    nlinarith [hs]
  rw [integral_const_mul, integral_add hxi hyi] at hbound
  have hsum := add_le_add (integral_sq_sigma_outer_le (dxLp u))
    (integral_sq_sigma_outer_le (dyLp u))
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 32 * ‖d‖ ^ 2)
  nlinarith

end KsIndex.Trace
