module

public import KsIndexLean.SphericalJoinedMass

@[expose] public section


open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace KsIndex.Spherical
open KsIndex.WeakH1

lemma disk_L2_mass_eq_norm_sq (f : L2C) :
    (∫⁻ z in (disk : Set ℂ), ENNReal.ofReal (‖f z‖ ^ 2)) = ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := (f : ℂ → ℂ))
    (μ := volume.restrict (disk : Set ℂ)) (by norm_num : (0 : ℝ) < 2)
  have he : eLpNorm' (f : ℂ → ℂ) 2 (volume.restrict (disk : Set ℂ)) = ‖f‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp f).aestronglyMeasurable]
    norm_num
  rw [he] at h
  simpa only [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

/-- Global canonical squared mass compared directly with the adopted disk L2 norms. -/
theorem sphereJoinedValue_mass_norm_comparison (u v : ComplexH1) :
    ENNReal.ofReal (‖valueCLM u‖ ^ 2 + ‖valueCLM v‖ ^ 2) ≤
      (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2) ∂(volume : Measure Ambient).toSphere) ∧
    (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2) ∂(volume : Measure Ambient).toSphere) ≤
      4 * ENNReal.ofReal (‖valueCLM u‖ ^ 2 + ‖valueCLM v‖ ^ 2) := by
  simpa only [disk_L2_mass_eq_norm_sq, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using
    sphereJoinedValue_mass_comparison u v

lemma sphereJoinedValue_mass_ne_top (u v : ComplexH1) :
    (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2)
      ∂(volume : Measure Ambient).toSphere) ≠ ∞ := by
  apply ne_of_lt
  exact (sphereJoinedValue_mass_norm_comparison u v).2.trans_lt
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)

/-- Real squared-mass comparison, after proving finiteness. -/
theorem sphereJoinedValue_mass_real_comparison (u v : ComplexH1) :
    ‖valueCLM u‖ ^ 2 + ‖valueCLM v‖ ^ 2 ≤
      (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2)
        ∂(volume : Measure Ambient).toSphere).toReal ∧
    (∫⁻ p, ENNReal.ofReal (‖sphereJoinedValue u v p‖ ^ 2)
      ∂(volume : Measure Ambient).toSphere).toReal ≤
      4 * (‖valueCLM u‖ ^ 2 + ‖valueCLM v‖ ^ 2) := by
  have h := sphereJoinedValue_mass_norm_comparison u v
  have h1 := ENNReal.toReal_mono (sphereJoinedValue_mass_ne_top u v) h.1
  have h2 := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) h.2
  constructor
  · simpa only [ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) (sq_nonneg _))] using h1
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) (sq_nonneg _))] using h2

end KsIndex.Spherical
