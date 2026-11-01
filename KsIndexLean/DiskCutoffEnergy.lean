module

public import KsIndexLean.DiskCutoffBounds

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk

lemma cutoffDiskExtension_value_energy_le (u : ComplexH1) :
    (∫ z : ℂ, ‖cutoffDiskExtension u z‖ ^ 2) ≤ 17 * ‖valueCLM u‖ ^ 2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.ball (0 : ℂ) 2) (fun z hz => by rw [cutoffDiskExtension_zero_outside u hz]; simp)]
  apply le_trans _ (diskExtension_value_energy_le u)
  have h1 := ((cutoffDiskExtension_spec u).2.1).mono_measure
    (Measure.restrict_le_self : volume.restrict (Metric.ball (0 : ℂ) 2) ≤ volume)
  have h2 := diskExtension_value_memLp u
  apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm h1.aestronglyMeasurable).mp h1)
    ((memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2)
  exact Filter.Eventually.of_forall fun z =>
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cutoffDiskExtension_norm_le u z)

lemma cutoffDiskExtension_direction_energy_le (u : ComplexH1) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖fderiv ℝ (diskExtensionCutoff : ℂ → ℝ) z‖ ≤ C) (d : ℂ) :
    (∫ z : ℂ, ‖cutoffDiskExtensionJet u z d‖ ^ 2) ≤
      1028 * ‖d‖ ^ 2 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) +
        34 * C ^ 2 * ‖d‖ ^ 2 * ‖valueCLM u‖ ^ 2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Metric.ball (0 : ℂ) 2) (fun z hz => by rw [cutoffDiskExtensionJet_zero_outside u hz]; simp)]
  have hj := ((cutoffDiskExtension_spec u).2.2 d).mono_measure
    (Measure.restrict_le_self : volume.restrict (Metric.ball (0 : ℂ) 2) ≤ volume)
  have hJ := diskExtension_direction_memLp u d
  have hV := diskExtension_value_memLp u
  have hiJ := (memLp_two_iff_integrable_sq_norm hJ.aestronglyMeasurable).mp hJ
  have hiV := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
  have hb : (∫ z in Metric.ball (0 : ℂ) 2, ‖cutoffDiskExtensionJet u z d‖ ^ 2) ≤
      ∫ z in Metric.ball (0 : ℂ) 2,
        2 * ‖diskExtensionJet u z d‖ ^ 2 +
          (2 * C ^ 2 * ‖d‖ ^ 2) * ‖refl 1 (valueCLM u) z‖ ^ 2 := by
    apply integral_mono_ae ((memLp_two_iff_integrable_sq_norm hj.aestronglyMeasurable).mp hj)
      ((hiJ.const_mul 2).add (hiV.const_mul _))
    apply Filter.Eventually.of_forall
    intro z
    simp only [Pi.add_apply]
    have hn := cutoffDiskExtensionJet_norm_le u hC z d
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [sq_nonneg (‖diskExtensionJet u z d‖ - C * ‖d‖ * ‖refl 1 (valueCLM u) z‖)]
  rw [integral_add (hiJ.const_mul 2) (hiV.const_mul _), integral_const_mul,
    integral_const_mul] at hb
  have hv := mul_le_mul_of_nonneg_left (diskExtension_value_energy_le u)
    (by positivity : 0 ≤ 2 * C ^ 2 * ‖d‖ ^ 2)
  have hd := diskExtension_direction_energy_le u d
  nlinarith

/-- One constant controls the whole-plane Cartesian H1 energy for every disk input. -/
theorem cutoffDiskExtension_uniform_energy :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : ComplexH1,
      (∫ z : ℂ, ‖cutoffDiskExtension u z‖ ^ 2) +
      (∫ z : ℂ, ‖cutoffDiskExtensionJet u z 1‖ ^ 2) +
      (∫ z : ℂ, ‖cutoffDiskExtensionJet u z Complex.I‖ ^ 2) ≤ K * ‖u‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := diskExtensionCutoff_derivative_bound
  refine ⟨2073 + 68 * C ^ 2, by positivity, ?_⟩
  intro u
  have hv := cutoffDiskExtension_value_energy_le u
  have hx := cutoffDiskExtension_direction_energy_le u hC0 hC 1
  have hy := cutoffDiskExtension_direction_energy_le u hC0 hC Complex.I
  simp only [norm_one, Complex.norm_I, one_pow, mul_one] at hx hy
  rw [coordinate_graph_norm_sq]
  have hn : 0 ≤ (17 + 68 * C ^ 2) * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) := by positivity
  nlinarith [sq_nonneg ‖valueCLM u‖]

end KsIndex.Trace
