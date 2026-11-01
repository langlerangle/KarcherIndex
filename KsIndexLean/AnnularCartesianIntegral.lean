module

public import KsIndexLean.ReconstructionPolarFormula

@[expose] public section


open Set MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section
namespace KsIndex.Trace

lemma integrableOn_continuous_real_smul {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {S : ℂ → ℝ} (hS : Continuous S) {u : ℂ → ℂ}
    (hu : MemLp u 2 (volume.restrict (annulusSet a b))) :
    IntegrableOn (fun z => S z • u z) (annulusSet a b) volume := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) b).exists_bound_of_continuousOn hS.continuousOn
  apply integrableOn_bdd_smul ha hab (C := C) hS.aestronglyMeasurable.restrict _ hu
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  have hzB : z ∈ Metric.closedBall (0 : ℂ) b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2.le
  simpa only [Real.norm_eq_abs] using hC z hzB

/-- The raw polar identities imply the real-coordinate test identity on the actual annulus. -/
theorem annular_cartesian_integral_one {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u v q : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b v) 1)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (sliceLp a b u r, sliceLp a b q r) ∈ circleAngularGraph)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψa : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hψb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ z in annulusSet a b, fderiv ℝ ψ z 1 • u z + ψ z • reconstructedX v q z) = 0 := by
  have hd : Continuous (fun z => fderiv ℝ ψ z 1) :=
    (contDiff_infty_iff_fderiv.mp hψ).2.continuous.clm_apply continuous_const
  have hi := (integrableOn_continuous_real_smul ha hab hd hu).add
    (integrableOn_continuous_real_smul ha hab hψ.continuous (memLp_reconstructedX ha hv hq))
  change IntegrableOn (fun z => fderiv ℝ ψ z 1 • u z + ψ z • reconstructedX v q z)
    (annulusSet a b) volume at hi
  trans ∫ r in Ioo a b, ∫ w : Circle₁, rawCartesianOne ψ u v q r w ∂circleMeasure
  · rw [integral_annulus_eq_weighted ha hi.aestronglyMeasurable,
      MeasureTheory.integral_prod _ (integrable_weighted_pullback ha hi)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => weighted_reconstruction_X ψ u v q (ha.trans hr.1) w
  · simpa only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] using
      raw_cartesian_identity_one ha hab hu hv hq hw hθ hψ hψa hψb

/-- The imaginary-coordinate annular test identity has the reconstructed complementary field. -/
theorem annular_cartesian_integral_I {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u v q : ℂ → ℂ} (hu : MemLp u 2 (volume.restrict (annulusSet a b)))
    (hv : MemLp v 2 (volume.restrict (annulusSet a b)))
    (hq : MemLp q 2 (volume.restrict (annulusSet a b)))
    (hw : TauCeti.HasWeakLineDerivOn volume (intervalOpens a b)
      (sliceLp a b u) (sliceLp a b v) 1)
    (hθ : ∀ᵐ r ∂volume.restrict (Ioo a b),
      (sliceLp a b u r, sliceLp a b q r) ∈ circleAngularGraph)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψa : ∀ w : Circle₁, ψ (a • (w : ℂ)) = 0)
    (hψb : ∀ w : Circle₁, ψ (b • (w : ℂ)) = 0) :
    (∫ z in annulusSet a b, fderiv ℝ ψ z Complex.I • u z + ψ z • reconstructedY v q z) = 0 := by
  have hd : Continuous (fun z => fderiv ℝ ψ z Complex.I) :=
    (contDiff_infty_iff_fderiv.mp hψ).2.continuous.clm_apply continuous_const
  have hi := (integrableOn_continuous_real_smul ha hab hd hu).add
    (integrableOn_continuous_real_smul ha hab hψ.continuous (memLp_reconstructedY ha hv hq))
  change IntegrableOn (fun z => fderiv ℝ ψ z Complex.I • u z + ψ z • reconstructedY v q z)
    (annulusSet a b) volume at hi
  trans ∫ r in Ioo a b, ∫ w : Circle₁, rawCartesianI ψ u v q r w ∂circleMeasure
  · rw [integral_annulus_eq_weighted ha hi.aestronglyMeasurable,
      MeasureTheory.integral_prod _ (integrable_weighted_pullback ha hi)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => weighted_reconstruction_Y ψ u v q (ha.trans hr.1) w
  · simpa only [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] using
      raw_cartesian_identity_I ha hab hu hv hq hw hθ hψ hψa hψb

end KsIndex.Trace
