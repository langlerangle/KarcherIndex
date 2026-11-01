module

public import KsIndexLean.DiskCutoffExtension

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

lemma diskExtensionCutoff_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := continuous_compact_norm_bound
    ((show ContDiff ℝ (⊤ : ℕ∞) (diskExtensionCutoff : ℂ → ℝ) from
      diskExtensionCutoff.contDiff).continuous_fderiv (by norm_num))
    (diskExtensionCutoff.hasCompactSupport.fderiv (𝕜 := ℝ))
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

lemma cutoffDiskExtension_norm_le (u : ComplexH1) (z : ℂ) :
    ‖cutoffDiskExtension u z‖ ≤ ‖refl 1 (valueCLM u) z‖ := by
  rw [cutoffDiskExtension, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg diskExtensionCutoff.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) diskExtensionCutoff.le_one

lemma cutoffDiskExtensionJet_norm_le (u : ComplexH1) {C : ℝ}
    (hC : ∀ z, ‖fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z‖ ≤ C) (z d : ℂ) :
    ‖cutoffDiskExtensionJet u z d‖ ≤
      ‖diskExtensionJet u z d‖ + C * ‖d‖ * ‖refl 1 (valueCLM u) z‖ := by
  have hd := (fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z).le_opNorm d
  have hd' : ‖fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z d‖ ≤ C * ‖d‖ :=
    hd.trans (mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
  change ‖diskExtensionCutoff z • diskExtensionJet u z d +
    (fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z d) • refl 1 (valueCLM u) z‖ ≤ _
  calc
    _ ≤ ‖diskExtensionCutoff z • diskExtensionJet u z d‖ +
      ‖(fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z d) • refl 1 (valueCLM u) z‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg diskExtensionCutoff.nonneg]
      exact add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) diskExtensionCutoff.le_one)
        (mul_le_mul_of_nonneg_right hd' (norm_nonneg _))

lemma cutoffDiskExtension_zero_outside (u : ComplexH1) {z : ℂ}
    (hz : z ∉ Metric.ball (0 : ℂ) 2) : cutoffDiskExtension u z = 0 := by
  have hn : z ∉ tsupport (diskExtensionCutoff : ℂ → ℝ) :=
    fun h => hz (diskExtensionCutoff_support h)
  simp [cutoffDiskExtension, image_eq_zero_of_notMem_tsupport hn]

lemma cutoffDiskExtensionJet_zero_outside (u : ComplexH1) {z : ℂ}
    (hz : z ∉ Metric.ball (0 : ℂ) 2) : cutoffDiskExtensionJet u z = 0 := by
  have hn : z ∉ tsupport (diskExtensionCutoff : ℂ → ℝ) :=
    fun h => hz (diskExtensionCutoff_support h)
  simp [cutoffDiskExtensionJet, image_eq_zero_of_notMem_tsupport hn,
    fderiv_of_notMem_tsupport ℝ hn]

end KsIndex.Trace
