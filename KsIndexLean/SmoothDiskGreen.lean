module

public import KsIndexLean.JacobiWeakTrace
public import KsIndexLean.FirstGreen
public import KsIndexLean.GreenIdentity
public import KsIndexLean.WeakH1Integration

@[expose] public section


noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.GradOrtho KsIndex.Surface

/-- First Green identity on globally smooth disk data, with the actual unnormalized
arclength measure. The conjugate is on the differentiated first argument. -/
lemma first_green_global (u v : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ 1 v) :
    (∫ w in (WeakH1.disk : Set ℂ), gradInner u v w + (starRingEnd ℂ) (laplacian u w) * v w) =
      ∫ w : Circle₁, (starRingEnd ℂ) (fderiv ℝ u w w) * v w ∂circleMeasure := by
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hgrad : Continuous (gradInner u v) := by
    unfold gradInner
    exact (((hdu.clm_apply continuous_const).star).mul
      (hdv.clm_apply continuous_const)).add
      (((hdu.clm_apply continuous_const).star).mul (hdv.clm_apply continuous_const))
  have hlap : Continuous (laplacian u) := continuous_iff_continuousAt.mpr
    (fun _ => KsIndex.Green.laplacian_continuousAt hu.contDiffAt)
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
    exact ((hu.contDiffAt.fderiv_right (m := 1) (by simp)).clm_apply
      contDiffAt_const).differentiableAt (by simp)
  have hg := KsIndex.FirstGreen.first_green_disk (fun w _ => hsecond 1 w)
    (fun w _ => hsecond Complex.I w) (fun w _ => (hv.differentiable (by simp) w))
    (hflux 1) (hflux Complex.I) hint
  have hc : Continuous (fun w : Circle₁ => (starRingEnd ℂ) (fderiv ℝ u w w) * v w) :=
    (((hdu.comp continuous_subtype_val).clm_apply continuous_subtype_val).star).mul
      (hv.continuous.comp continuous_subtype_val)
  rw [integral_circleMeasure_window (-Real.pi) hc.aestronglyMeasurable]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  calc
    _ = _ := hg
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [circleParam_coe]
      rw [hwithin _ (by simp [Metric.mem_closedBall, dist_zero_right,
        Complex.norm_exp_ofReal_mul_I])]

/-- The actual weak Jacobi form on smooth encodings equals the boundary
normal-derivative pairing when the first function solves the Jacobi PDE.
No natural boundary condition is assumed. -/
lemma weakJacobi_globalSmooth_green (V : BoundedRealPotential)
    (u v : ℂ → ℂ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hjac : ∀ w ∈ (WeakH1.disk : Set ℂ), laplacian u w + (V.V w : ℂ) * u w = 0) :
    weakJacobi V (globalSmoothH1 u hu) (globalSmoothH1 v hv) =
      ∫ w : Circle₁, (starRingEnd ℂ) (fderiv ℝ u w w) * v w ∂circleMeasure := by
  have hp : Integrable (fun w => (V.V w : ℂ) * (starRingEnd ℂ) (u w) * v w)
      (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (potential_integrable V (globalSmoothH1 u hu) (globalSmoothH1 v hv)).congr
    filter_upwards [globalSmoothH1_value u hu, globalSmoothH1_value v hv] with w h1 h2
    rw [h1, h2]
  have hg : Integrable (gradInner u v) (volume.restrict (WeakH1.disk : Set ℂ)) := by
    apply (dirichlet_integrable (globalSmoothH1 u hu) (globalSmoothH1 v hv)).congr
    filter_upwards [globalSmoothH1_dx u hu, globalSmoothH1_dy u hu,
      globalSmoothH1_dx v hv, globalSmoothH1_dy v hv] with w h1 h2 h3 h4
    simp only [gradInner, h1, h2, h3, h4]
  rw [weakJacobi_integral_representatives V _ _ (globalSmoothH1_value u hu)
    (globalSmoothH1_value v hv) (globalSmoothH1_dx u hu) (globalSmoothH1_dy u hu)
    (globalSmoothH1_dx v hv) (globalSmoothH1_dy v hv)]
  change (∫ w in (WeakH1.disk : Set ℂ), gradInner u v w) - _ = _
  rw [← integral_sub hg hp, ← first_green_global u v hu (hv.of_le (by simp))]
  apply setIntegral_congr_fun WeakH1.disk.isOpen.measurableSet
  intro w hw
  have hl : laplacian u w = -((V.V w : ℂ) * u w) := eq_neg_of_add_eq_zero_left (hjac w hw)
  dsimp only
  rw [hl, map_neg, map_mul, Complex.conj_ofReal]
  ring

lemma fderiv_radial_of_hasDerivAt (f : ℂ → ℂ) {w a : ℂ}
    (hf : DifferentiableAt ℝ f w)
    (hd : HasDerivAt (fun r : ℝ => f ((r : ℂ) * w)) a 1) :
    fderiv ℝ f w w = a := by
  have hr := (hasDerivAt_id (1 : ℝ)).ofReal_comp.mul_const w
  have hff : HasFDerivAt f (fderiv ℝ f w) ((1 : ℂ) * w) := by
    simpa using hf.hasFDerivAt
  have hc := hff.comp_hasDerivAt (1 : ℝ) hr
  have hc' : HasDerivAt (fun r : ℝ => f ((r : ℂ) * w)) (fderiv ℝ f w w) 1 := by
    convert hc using 1 <;> first | rfl | simp only [Complex.ofReal_one, one_mul]
  exact hc'.unique hd

/-- The vertical translation field's actual normal derivative in Green's formula. -/
lemma verticalThree_normal {w : ℂ} (hw : ‖w‖ = 1) :
    fderiv ℝ (JacobiFields.nu3 3) w w = 2 :=
  fderiv_radial_of_hasDerivAt _
    ((JacobiFields.nu3_contDiff 3 (by decide)).differentiable (by simp) w)
    (JacobiFields.nu3_three_radial_derivative hw)

/-- Boundary flux pairing of the vertical H1 field with globally smooth data:
twice the unnormalized boundary integral of the test. Extension to arbitrary
weak tests requires a separate argument. -/
lemma verticalThree_smooth_green (v : ℂ → ℂ) (hv : ContDiff ℝ ∞ v) :
    weakJacobi (surfacePotential 3) verticalThreeH1 (globalSmoothH1 v hv) =
      (2 : ℂ) * ∫ w : Circle₁, v w ∂circleMeasure := by
  have h := weakJacobi_globalSmooth_green (surfacePotential 3) (JacobiFields.nu3 3) v
    (JacobiFields.nu3_contDiff 3 (by decide)) hv
    (fun w _ => JacobiFields.jacobi_nu3 3 (by decide) w)
  change weakJacobi (surfacePotential 3)
    (globalSmoothH1 (JacobiFields.nu3 3) (JacobiFields.nu3_contDiff 3 (by decide))) _ = _
  rw [h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [verticalThree_normal (by simpa [Metric.mem_sphere, dist_zero_right] using w.property)]
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    exact map_ofNat (starRingEnd ℂ) 2
  rw [htwo]

lemma verticalThree_smooth_trace_green (v : ℂ → ℂ) (hv : ContDiff ℝ ∞ v) :
    weakJacobi (surfacePotential 3) verticalThreeH1 (globalSmoothH1 v hv) =
      (2 : ℂ) * ∫ w : Circle₁, diskTraceCLM (globalSmoothH1 v hv) w ∂circleMeasure := by
  rw [verticalThree_smooth_green v hv]
  exact congrArg (fun z : ℂ => 2 * z) (integral_congr_ae (globalSmoothH1_trace v hv).symm)

end KsIndex.Trace
