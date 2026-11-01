module

public import KsIndexLean.AngularProductJet
public import KsIndexLean.SupportedSeamCutoff

@[expose] public section


open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Arbitrary genuine seam-domain weak regularity localizes to the explicit planar cutoff field. -/
theorem seamDomain_cutoff_localization {A : Set Circle₁} (hA : IsOpen A)
    {η : ℂ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hs : ∀ w : Circle₁, w ∉ A → η =ᶠ[𝓝 (w : ℂ)] (fun _ => 0))
    (u v : ComplexH1) (c : ℂ) {J : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume (seamDomain A hA) (joinedDiskValue u v c) J) :
    TauCeti.HasWeakFDerivOn volume (annulusOpens (1 / 2) 2) (cutoffDiskValue η u v c)
      (reconstructedJet (cutoffDiskRadial η u v c) (cutoffDiskAngular η u v c)) := by
  have hΩ : seamDomain A hA ≤ annulusOpens (1 / 2) 2 := fun _ hz => hz.1
  have hj := hw.congr_ae_deriv (joinedDiskJet_unique hΩ u v c hw)
  have he := weakF_smooth_mul_supported_annulus (by norm_num) (by norm_num) hΩ
    (angularCoefficient_contDiffOn (by norm_num) hη) (angularCutoff_support_in_seamDomain hA hs)
    hj (memLp_cutoffDiskValue hη.continuous u v c) (memLp_cutoffDisk_productJet hη u v c)
  apply he.congr_ae_deriv
  filter_upwards [ae_restrict_mem measurableSet_annulusSet] with z hz
  exact cutoffDisk_productJet_eq hη u v c
    (norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz.1))

end KsIndex.Trace
