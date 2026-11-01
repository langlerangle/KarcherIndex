module

public import KsIndexLean.EndChartL2Anchor
public import KsIndexLean.GammaRemovability

@[expose] public section


/-! Full-ball real value/gradient L² from classical punctured regularity and
finite derivative energy. No PDE or near-puncture boundedness is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace KsIndex.EndChart
open KsIndex.PunctureRemoval

lemma norm_gradEnc_eq (v : ℂ → ℝ) (z : ℂ) :
    ‖gradEnc v z‖ = ‖fderiv ℝ v z‖ := by
  rw [← innerSL_gradEnc v z, innerSL_apply_norm]

theorem memLp_gradEnc_of_contDiffAt_energy
    {R r₀ : ℝ} (hRr : R < r₀) (v : ℂ → ℝ)
    (hsm : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ → ContDiffAt ℝ 2 v z)
    (hE : (∫⁻ z in puncturedDisk R, ‖fderiv ℝ v z‖ₑ ^ 2 ∂volume) ≠ ⊤) :
    MemLp (gradEnc v) 2 (volume.restrict (puncturedDisk R)) := by
  have hc : ContinuousOn (fderiv ℝ v) (puncturedDisk R) := by
    intro z hz
    exact ((hsm z hz.1 (lt_of_le_of_lt hz.2 hRr)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  have hd : MemLp (fderiv ℝ v) 2 (volume.restrict (puncturedDisk R)) := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num)
      (hc.aestronglyMeasurable (measurableSet_puncturedDisk R))]
    simpa using (lt_top_iff_ne_top.mpr hE)
  have hg : ContinuousOn (gradEnc v) (puncturedDisk R) := by
    intro z hz
    have hcont := (hsm z hz.1 (lt_of_le_of_lt hz.2 hRr)).continuousAt_fderiv
      (by norm_num)
    apply ContinuousAt.continuousWithinAt
    have heq : gradEnc v = fun x =>
        Complex.ofRealCLM ((fderiv ℝ v x) 1) +
        Complex.ofRealCLM ((fderiv ℝ v x) Complex.I) * Complex.I := by
      funext x
      apply Complex.ext <;> simp [gradEnc]
    rw [heq]
    exact (Complex.ofRealCLM.continuous.continuousAt.comp
      (hcont.clm_apply continuousAt_const)).add
      ((Complex.ofRealCLM.continuous.continuousAt.comp
        (hcont.clm_apply continuousAt_const)).mul continuousAt_const)
  apply hd.of_le (hg.aestronglyMeasurable (measurableSet_puncturedDisk R))
  exact Filter.Eventually.of_forall (fun z => (norm_gradEnc_eq v z).le)

theorem memLp_value_gradEnc_ball_of_contDiffAt_energy
    {R r₀ : ℝ} (hR : 0 < R) (hRr : R < r₀) (v : ℂ → ℝ)
    (hsm : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ → ContDiffAt ℝ 2 v z)
    (hE : (∫⁻ z in puncturedDisk R, ‖fderiv ℝ v z‖ₑ ^ 2 ∂volume) ≠ ⊤) :
    MemLp v 2 (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
      MemLp (gradEnc v) 2 (volume.restrict (Metric.ball (0 : ℂ) R)) :=
  ⟨memLp_ball_of_memLp_puncturedDisk
      (memLp_two_of_contDiffAt_energy hR hRr v hsm hE),
    memLp_ball_of_memLp_puncturedDisk
      (memLp_gradEnc_of_contDiffAt_energy hRr v hsm hE)⟩

/-- The three full-chart integrability inputs of complex puncture removal.
The two finite-energy premises are the remaining geometric transport obligations. -/
theorem memLp_complex_jet_ball_of_component_energy
    {R r₀ : ℝ} (hR : 0 < R) (hRr : R < r₀) (F : ℂ → ℂ)
    (hsm : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r₀ → ContDiffAt ℝ 2 F z)
    (hEr : (∫⁻ z in puncturedDisk R,
      ‖fderiv ℝ (fun w => (F w).re) z‖ₑ ^ 2 ∂volume) ≠ ⊤)
    (hEi : (∫⁻ z in puncturedDisk R,
      ‖fderiv ℝ (fun w => (F w).im) z‖ₑ ^ 2 ∂volume) ≠ ⊤) :
    MemLp F 2 (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
    MemLp (gradEnc (fun w => (F w).re)) 2
      (volume.restrict (Metric.ball (0 : ℂ) R)) ∧
    MemLp (gradEnc (fun w => (F w).im)) 2
      (volume.restrict (Metric.ball (0 : ℂ) R)) := by
  have hr := memLp_value_gradEnc_ball_of_contDiffAt_energy hR hRr
    (fun w => (F w).re)
    (fun z hz hzr => Complex.reCLM.contDiff.contDiffAt.comp z (hsm z hz hzr)) hEr
  have hi := memLp_value_gradEnc_ball_of_contDiffAt_energy hR hRr
    (fun w => (F w).im)
    (fun z hz hzr => Complex.imCLM.contDiff.contDiffAt.comp z (hsm z hz hzr)) hEi
  refine ⟨?_, hr.2, hi.2⟩
  have h := (Complex.ofRealCLM.comp_memLp' hr.1).add
    ((Complex.ofRealCLM.comp_memLp' hi.1).const_smul Complex.I)
  have heq : (fun z => Complex.ofRealCLM ((F z).re)) +
      Complex.I • (fun z => Complex.ofRealCLM ((F z).im)) = F := by
    funext z
    apply Complex.ext <;> simp
  change MemLp ((fun z => Complex.ofRealCLM ((F z).re)) +
      Complex.I • (fun z => Complex.ofRealCLM ((F z).im))) 2 _ at h
  rwa [heq] at h

end KsIndex.EndChart
