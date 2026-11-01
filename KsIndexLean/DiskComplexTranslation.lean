module

public import KsIndexLean.DiskExtensionTranslation
public import KsIndexLean.DiskProjectionEnergy

@[expose] public section


noncomputable section
open Set MeasureTheory TopologicalSpace TauCeti
open scoped ENNReal
namespace KsIndex.Trace
open KsIndex.WeakH1

lemma eLpNorm_complex_le_re_add_im {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ≤ eLpNorm (fun z => (f z).re) 2 volume +
      eLpNorm (fun z => (f z).im) 2 volume := by
  have hr : AEStronglyMeasurable (fun z => (f z).re) volume :=
    Complex.reCLM.continuous.comp_aestronglyMeasurable hf
  have hi : AEStronglyMeasurable (fun z => (f z).im) volume :=
    Complex.imCLM.continuous.comp_aestronglyMeasurable hf
  calc
    _ ≤ eLpNorm (fun z => ‖(f z).re‖ + ‖(f z).im‖) 2 volume := by
      apply eLpNorm_mono hf
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact Complex.norm_le_abs_re_add_abs_im (f z)
    _ ≤ eLpNorm (fun z => ‖(f z).re‖) 2 volume +
        eLpNorm (fun z => ‖(f z).im‖) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ = _ := by rw [eLpNorm_norm _ hr, eLpNorm_norm _ hi]

lemma diskExtension_complex_translation_le (u : ComplexH1) (h : ℂ) :
    eLpNorm (fun z => cutoffDiskExtension u (z + h) - cutoffDiskExtension u z) 2 volume ≤
      ‖h‖ₑ * (‖W1p.gradient (diskExtensionRealH1 Complex.reCLM u)‖ₑ +
        ‖W1p.gradient (diskExtensionRealH1 Complex.imCLM u)‖ₑ) := by
  have hf := (cutoffDiskExtension_spec u).2.1.aestronglyMeasurable
  have ht := hf.comp_quasiMeasurePreserving
    (measurePreserving_add_right (volume : Measure ℂ) h).quasiMeasurePreserving
  have he := eLpNorm_complex_le_re_add_im (ht.sub hf)
  dsimp only [Function.comp_apply, Pi.sub_apply] at he
  simp only [Complex.sub_re, Complex.sub_im] at he
  exact he.trans (by
    rw [mul_add]
    exact add_le_add (diskExtensionReal_translation_le Complex.reCLM u h)
      (diskExtensionReal_translation_le Complex.imCLM u h))

/-- Uniform linear translation modulus for the entire unrestricted disk unit ball. -/
theorem diskExtension_unitBall_translation_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ComplexH1), ‖u‖ ≤ 1 → ∀ h : ℂ,
      eLpNorm (fun z => cutoffDiskExtension u (z + h) - cutoffDiskExtension u z) 2 volume
        ≤ ‖h‖ₑ * ENNReal.ofReal C := by
  obtain ⟨K, hK, hbound⟩ := diskExtensionRealH1_uniform_gradient_energy
  let C := (‖Complex.reCLM‖ ^ 2 + ‖Complex.imCLM‖ ^ 2) * K + 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro u hu h
  have hu2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hb (L : ℂ →L[ℝ] ℝ) :
      ‖W1p.gradient (diskExtensionRealH1 L u)‖ ≤ ‖L‖ ^ 2 * K + 1 := by
    have he := (hbound L u).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hu2 hK) (sq_nonneg ‖L‖))
    simp only [mul_one] at he
    have ha : 0 ≤ ‖L‖ ^ 2 * K := mul_nonneg (sq_nonneg _) hK
    nlinarith [sq_nonneg (‖L‖ ^ 2 * K)]
  have hs : ‖W1p.gradient (diskExtensionRealH1 Complex.reCLM u)‖ +
      ‖W1p.gradient (diskExtensionRealH1 Complex.imCLM u)‖ ≤ C := by
    dsimp [C]
    nlinarith [hb Complex.reCLM, hb Complex.imCLM]
  apply (diskExtension_complex_translation_le u h).trans
  apply mul_le_mul_right
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_mono hs

/-- The uniform small-translation hypothesis of Frechet--Kolmogorov. -/
theorem diskExtension_unitBall_small_translations {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ u : ComplexH1, ‖u‖ ≤ 1 → ∀ h : ℂ, ‖h‖ < δ →
      eLpNorm (fun z => cutoffDiskExtension u (z + h) - cutoffDiskExtension u z) 2 volume ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := diskExtension_unitBall_translation_bound
  rcases eq_or_ne ε ∞ with rfl | htop
  · exact ⟨1, zero_lt_one, fun _ _ _ _ => le_top⟩
  let δ := ε.toReal / (C + 1)
  have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hε.ne' htop) (by linarith)
  refine ⟨δ, hδ, fun u hu h hh => (hbound u hu h).trans ?_⟩
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg h), ← ENNReal.ofReal_toReal htop]
  apply ENNReal.ofReal_mono
  calc
    ‖h‖ * C ≤ δ * C := mul_le_mul_of_nonneg_right hh.le hC
    _ ≤ δ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
    _ = ε.toReal := div_mul_cancel₀ _ (by linarith)

end KsIndex.Trace
