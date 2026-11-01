module

public import KsIndexLean.OuterInversionEnergy
public import KsIndexLean.JoinedJetUniqueness

@[expose] public section


noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.SingleDisk KsIndex.Bracket

lemma ball_two_ae_disk_union_outer :
    Metric.ball (0 : ℂ) 2 =ᵐ[volume] (disk : Set ℂ) ∪ annulusSet (1 : ℝ) 2 := by
  filter_upwards [ae_norm_ne_one] with z hz
  apply propext
  change z ∈ Metric.ball (0 : ℂ) 2 ↔ z ∈ Metric.ball (0 : ℂ) 1 ∨ _
  simp only [Metric.mem_ball, dist_zero_right, mem_annulusSet]
  constructor
  · intro h
    rcases lt_or_gt_of_ne hz with hi | ho
    · exact Or.inl hi
    · exact Or.inr ⟨ho, h⟩
  · rintro (hi | ho)
    · linarith
    · exact ho.2

lemma integral_ball_two_split {f : ℂ → ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : ℂ) 2)) :
    (∫ z in Metric.ball (0 : ℂ) 2, f z) =
      (∫ z in (disk : Set ℂ), f z) + ∫ z in annulusSet (1 : ℝ) 2, f z := by
  rw [setIntegral_congr_set ball_two_ae_disk_union_outer]
  apply setIntegral_union
  · apply Set.disjoint_left.mpr
    intro z hi ho
    have h : ‖z‖ < 1 := KsIndex.SurfaceForm.mem_disk_iff.mp hi
    linarith [ho.1]
  · exact measurableSet_annulusSet
  · apply hf.mono_set
    intro z hz
    have h : ‖z‖ < 1 := KsIndex.SurfaceForm.mem_disk_iff.mp hz
    simpa only [Metric.mem_ball, dist_zero_right] using (show ‖z‖ < 2 by linarith)
  · apply hf.mono_set
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right] using hz.2

lemma diskExtension_value_energy_le (u : ComplexH1) :
    (∫ z in Metric.ball (0 : ℂ) 2, ‖refl 1 (valueCLM u) z‖ ^ 2) ≤
      17 * ‖valueCLM u‖ ^ 2 := by
  have hm := diskExtension_value_memLp u
  rw [integral_ball_two_split ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)]
  have hi : (∫ z in (disk : Set ℂ), ‖refl 1 (valueCLM u) z‖ ^ 2) = ‖valueCLM u‖ ^ 2 := by
    rw [lp_norm_sq]
    apply setIntegral_congr_fun disk.isOpen.measurableSet
    intro z hz
    dsimp only
    rw [full_boundary_even_eq_inner u (KsIndex.SurfaceForm.mem_disk_iff.mp hz)]
  have ho : (∫ z in annulusSet (1 : ℝ) 2, ‖refl 1 (valueCLM u) z‖ ^ 2) =
      ∫ z in annulusSet (1 : ℝ) 2, ‖valueCLM u (σ z)‖ ^ 2 := by
    apply setIntegral_congr_fun measurableSet_annulusSet
    intro z hz
    simp only [KsIndex.SingleDisk.refl, ite_eq_right (not_le.mpr hz.1), one_mul]
  rw [hi, ho]
  linarith [integral_sq_sigma_outer_le (valueCLM u)]

lemma diskExtension_inner_energy_le (u : ComplexH1) (d : ℂ) :
    (∫ z in (disk : Set ℂ), ‖diskExtensionJet u z d‖ ^ 2) ≤
      2 * ‖d‖ ^ 2 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) := by
  have hD : MemLp (fun z => Dxy (dxLp u) (dyLp u) z d) 2
      (volume.restrict (disk : Set ℂ)) :=
    ((Lp.memLp (dxLp u)).const_smul d.re).add ((Lp.memLp (dyLp u)).const_smul d.im)
  have hi := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).mp hD
  have hx := (memLp_two_iff_integrable_sq_norm (Lp.memLp (dxLp u)).aestronglyMeasurable).mp (Lp.memLp (dxLp u))
  have hy := (memLp_two_iff_integrable_sq_norm (Lp.memLp (dyLp u)).aestronglyMeasurable).mp (Lp.memLp (dyLp u))
  have he : (∫ z in (disk : Set ℂ), ‖diskExtensionJet u z d‖ ^ 2) =
      ∫ z in (disk : Set ℂ), ‖Dxy (dxLp u) (dyLp u) z d‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [diskExtensionJet_inner u] with z hz
    rw [← hz]
  rw [he]
  have hb : (∫ z in (disk : Set ℂ), ‖Dxy (dxLp u) (dyLp u) z d‖ ^ 2) ≤
      ∫ z in (disk : Set ℂ), (2 * ‖d‖ ^ 2) * (‖dxLp u z‖ ^ 2 + ‖dyLp u z‖ ^ 2) := by
    apply integral_mono_ae hi ((hx.add hy).const_mul _)
    apply Filter.Eventually.of_forall
    intro z
    simp only [Pi.add_apply]
    have hn : ‖Dxy (dxLp u) (dyLp u) z d‖ ≤ ‖d‖ * (‖dxLp u z‖ + ‖dyLp u z‖) := by
      rw [Dxy_apply]
      calc
        _ ≤ ‖d.re • dxLp u z‖ + ‖d.im • dyLp u z‖ := norm_add_le _ _
        _ ≤ ‖d‖ * ‖dxLp u z‖ + ‖d‖ * ‖dyLp u z‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm d) (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm d) (norm_nonneg _))
        _ = _ := by ring
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    have ha : (‖dxLp u z‖ + ‖dyLp u z‖) ^ 2 ≤ 2 * (‖dxLp u z‖ ^ 2 + ‖dyLp u z‖ ^ 2) := by
      nlinarith [sq_nonneg (‖dxLp u z‖ - ‖dyLp u z‖)]
    have hh := mul_le_mul_of_nonneg_left ha (sq_nonneg ‖d‖)
    nlinarith
  rw [integral_const_mul, integral_add hx hy, ← lp_norm_sq, ← lp_norm_sq] at hb
  exact hb

lemma diskExtension_direction_energy_le (u : ComplexH1) (d : ℂ) :
    (∫ z in Metric.ball (0 : ℂ) 2, ‖diskExtensionJet u z d‖ ^ 2) ≤
      514 * ‖d‖ ^ 2 * (‖dxLp u‖ ^ 2 + ‖dyLp u‖ ^ 2) := by
  have hm := diskExtension_direction_memLp u d
  rw [integral_ball_two_split ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)]
  linarith [diskExtension_inner_energy_le u d, diskExtension_outer_energy_le u d]

end KsIndex.Trace
