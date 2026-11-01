module

public import KsIndexLean.DiskExtensionRealization

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma projectedGradientRaw_sq_le (L : ℂ →L[ℝ] ℝ) (J : ℂ → ℂ →L[ℝ] ℂ) (z : ℂ) :
    ‖projectedGradientRaw L J z‖ ^ 2 ≤
      ‖L‖ ^ 2 * (‖J z 1‖ ^ 2 + ‖J z Complex.I‖ ^ 2) := by
  have hx := L.le_opNorm (J z 1)
  have hy := L.le_opNorm (J z Complex.I)
  have hx2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hx
  have hy2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 hy
  simp only [Real.norm_eq_abs, sq_abs] at hx2 hy2
  have he : ‖projectedGradientRaw L J z‖ ^ 2 =
      (L (J z 1)) ^ 2 + (L (J z Complex.I)) ^ 2 := by
    rw [Complex.sq_norm]
    simp [projectedGradientRaw, Complex.normSq_apply, pow_two]
  rw [he]
  nlinarith

/-- Projection preserves the Cartesian energy bound of the constructed weak extension. -/
lemma diskExtensionRealH1_gradient_energy_le (L : ℂ →L[ℝ] ℝ) (u : ComplexH1) :
    ‖W1p.gradient (diskExtensionRealH1 L u)‖ ^ 2 ≤ ‖L‖ ^ 2 *
      ((∫ z : ℂ, ‖cutoffDiskExtensionJet u z 1‖ ^ 2) +
       (∫ z : ℂ, ‖cutoffDiskExtensionJet u z Complex.I‖ ^ 2)) := by
  have hx := (cutoffDiskExtension_spec u).2.2 1
  have hy := (cutoffDiskExtension_spec u).2.2 Complex.I
  have hix := (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  have hiy := (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy
  let hg := W1p.gradient (diskExtensionRealH1 L u)
  have hnorm : ‖hg‖ ^ 2 = ∫ z : ℂ, ‖projectedGradientRaw L (cutoffDiskExtensionJet u) z‖ ^ 2 := by
    have he := L2.inner_def (𝕜 := ℝ) hg hg
    simp only [real_inner_self_eq_norm_sq, Opens.coe_top, Measure.restrict_univ] at he
    rw [he]
    apply integral_congr_ae
    filter_upwards [diskExtensionRealH1_gradient_ae L u] with z hz
    rw [hz]
  change ‖hg‖ ^ 2 ≤ _
  rw [hnorm, ← integral_add hix hiy, ← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun z => sq_nonneg _)
  · exact (hix.add hiy).const_mul _
  · exact Filter.Eventually.of_forall (projectedGradientRaw_sq_le L _)

/-- A single extension constant controls every real projected gradient. -/
theorem diskExtensionRealH1_uniform_gradient_energy :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℂ →L[ℝ] ℝ) (u : ComplexH1),
      ‖W1p.gradient (diskExtensionRealH1 L u)‖ ^ 2 ≤ ‖L‖ ^ 2 * (K * ‖u‖ ^ 2) := by
  obtain ⟨K, hK, hbound⟩ := cutoffDiskExtension_uniform_energy
  refine ⟨K, hK, fun L u => (diskExtensionRealH1_gradient_energy_le L u).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hv : 0 ≤ ∫ z : ℂ, ‖cutoffDiskExtension u z‖ ^ 2 :=
    integral_nonneg (fun z => sq_nonneg _)
  linarith [hbound u]

end KsIndex.Trace
