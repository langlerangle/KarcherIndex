module

public import KsIndexLean.AngularCoefficientDerivative

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- The full angular Leibniz term is exactly the smooth product-rule jet. -/
theorem angularProductJet_eq {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v q : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    η (nUnit z) • reconstructedJet v q z +
      (fderiv ℝ (fun w => η (nUnit w)) z).smulRight (u z) =
    reconstructedJet (angularCutoffField η v)
      (fun w => angularCutoffField η q w + angularCutoffField (angularTestDeriv η) u w) z := by
  apply clm_eq_of_radial_rotation hz
  · simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      reconstructedJet_radial v q hz, angularCoefficient_radial hη hz, zero_smul, add_zero,
      reconstructedJet_radial _ _ hz, angularCutoffField]
    exact smul_comm _ _ _
  · simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      reconstructedJet_rotation v q hz, angularCoefficient_rotation hη hz,
      reconstructedJet_rotation _ _ hz, angularCutoffField]

theorem cutoffDisk_productJet_eq {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    η (nUnit z) • joinedDiskJet u v c z +
      (fderiv ℝ (fun w => η (nUnit w)) z).smulRight (joinedDiskValue u v c z) =
    reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c) z :=
  angularProductJet_eq hη _ _ _ hz

lemma memLp_cutoffDisk_productJet {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (u v : ComplexH1) (c : ℂ) :
    MemLp (fun z => η (nUnit z) • joinedDiskJet u v c z +
      (fderiv ℝ (fun w => η (nUnit w)) z).smulRight (joinedDiskValue u v c z)) 2
      (volume.restrict (annulusSet (1 / 2 : ℝ) 2)) := by
  apply MemLp.ae_eq _ (memLp_cutoffDisk_jet hη u v c)
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact (cutoffDisk_productJet_eq hη u v c
    (norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz.1))).symm

end KsIndex.Trace
