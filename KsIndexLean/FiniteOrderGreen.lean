module

public import KsIndexLean.SmoothDiskGreen

@[expose] public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.GradOrtho KsIndex.Surface
/-- First Green identity for a C² first argument and a C¹ test on the disk,
with the actual unnormalized arclength measure and conjugated normal flux. -/
lemma first_green_C2 (u v : ℂ → ℂ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v) :
    (∫ w in (WeakH1.disk : Set ℂ), gradInner u v w + (starRingEnd ℂ) (laplacian u w) * v w) =
      ∫ w : Circle₁, (starRingEnd ℂ) (fderiv ℝ u w w) * v w ∂circleMeasure := by
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hgrad : Continuous (gradInner u v) := by
    unfold gradInner
    exact (((hdu.clm_apply continuous_const).star).mul
      (hdv.clm_apply continuous_const)).add
      (((hdu.clm_apply continuous_const).star).mul (hdv.clm_apply continuous_const))
  have hpartial (a : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ u z a) :=
    (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hlap : Continuous (laplacian u) :=
    (((hpartial 1).continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      (((hpartial Complex.I).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hint : IntegrableOn (fun w => gradInner u v w + (starRingEnd ℂ) (laplacian u w) * v w)
      (Metric.ball (0 : ℂ) 1) :=
    ((hgrad.add (hlap.star.mul hv.continuous)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set Metric.ball_subset_closedBall
  have hwithin (w : ℂ) (hw : w ∈ Metric.closedBall (0 : ℂ) 1) :
      fderivWithin ℝ u (Metric.closedBall 0 1) w = fderiv ℝ u w := by
    apply (hu.differentiable (by simp) w).hasFDerivAt.hasFDerivWithinAt.fderivWithin
    exact uniqueDiffOn_convex (convex_closedBall 0 1)
      (by rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
          exact ⟨0, Metric.mem_ball_self (by norm_num)⟩) w hw
  have hflux (a : ℂ) : ContinuousOn
      (fun w => (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) w a) * v w)
      (Metric.closedBall 0 1) := by
    have hraw : Continuous (fun w => (starRingEnd ℂ) (fderiv ℝ u w a) * v w) :=
      ((hdu.clm_apply continuous_const).star).mul hv.continuous
    apply hraw.continuousOn.congr
    intro w hw
    change (starRingEnd ℂ) (fderivWithin ℝ u (Metric.closedBall 0 1) w a) * v w =
      (starRingEnd ℂ) (fderiv ℝ u w a) * v w
    rw [hwithin w hw]
  have hsecond (a w : ℂ) : DifferentiableAt ℝ (fun z => fderiv ℝ u z a) w := by
    exact ((hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hg := KsIndex.FirstGreen.first_green_disk (fun w _ => hsecond 1 w)
    (fun w _ => hsecond Complex.I w) (fun w _ => (hv.differentiable (by simp) w))
    (hflux 1) (hflux Complex.I) hint
  have hc : Continuous (fun w : Circle₁ => (starRingEnd ℂ) (fderiv ℝ u w w) * v w) :=
    (((hdu.comp continuous_subtype_val).clm_apply continuous_subtype_val).star).mul
      (hv.continuous.comp continuous_subtype_val)
  rw [integral_circleMeasure_window (-Real.pi) hc.aestronglyMeasurable]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  calc
    _ = _ := hg
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [circleParam_coe]
      rw [hwithin _ (by simp [Metric.mem_closedBall, dist_zero_right,
        Complex.norm_exp_ofReal_mul_I])]


end KsIndex.Trace
