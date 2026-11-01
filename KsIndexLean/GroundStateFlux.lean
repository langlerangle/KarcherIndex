module

public import KsIndexLean.GroundStateTransform

@[expose] public section


/-! Energy control of the ground-state flux, without a singular boundary quotient. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.GroundState
open KsIndex.Trace KsIndex.Surface

def groundFlux (g f : ℂ → ℂ) (d z : ℂ) : ℂ :=
  g z * fderiv ℝ f z d - f z * fderiv ℝ g z d

lemma groundFlux_product {g v : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (hv : DifferentiableAt ℝ v z) (d : ℂ) :
    groundFlux g (fun w => g w * v w) d z = g z ^ 2 * fderiv ℝ v z d := by
  have hp := (hg.hasFDerivAt.mul hv.hasFDerivAt).fderiv
  change fderiv ℝ (fun w => g w * v w) z = _ at hp
  simp only [groundFlux, hp, add_apply, smul_apply, smul_eq_mul]
  ring

lemma continuous_groundFlux {g f : ℂ → ℂ} (hg : ContDiff ℝ 1 g)
    (hf : ContDiff ℝ 1 f) (d : ℂ) : Continuous (groundFlux g f d) :=
  (hg.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)).sub
    (hf.continuous.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const))

/-- The ground-state flux is controlled by energy without division at the boundary. -/
theorem groundFlux_multiple_bound (g v : ℂ → ℂ) (V : ℂ → ℝ) (M : ℝ)
    (hg : ContDiff ℝ 2 g) (hv : ContDiff ℝ 1 v)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian g z + V z * g z = 0)
    (hM : ∀ z ∈ (WeakH1.disk : Set ℂ), ‖g z‖ ^ 2 ≤ M) :
    (∫ z in (WeakH1.disk : Set ℂ),
      ‖groundFlux g (fun w => g w * v w) 1 z‖ ^ 2 +
      ‖groundFlux g (fun w => g w * v w) Complex.I z‖ ^ 2) ≤
      M * (∫ z in (WeakH1.disk : Set ℂ),
        gradSq (fun w => g w * v w) z - V z * ‖g z * v z‖ ^ 2) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hi (f : ℂ → ℝ) (hf : Continuous f) :
      IntegrableOn f (WeakH1.disk : Set ℂ) :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  have hweight := (hg.continuous.norm.pow 2).mul (KsIndex.PiAssembly.continuous_gradSq hv)
  rw [disk_ground_state_energy g v V hg hv hr hb he, ← integral_const_mul]
  apply setIntegral_mono_on
    (hi _ (((continuous_groundFlux hg1 (hg1.mul hv) 1).norm.pow 2).add
      ((continuous_groundFlux hg1 (hg1.mul hv) Complex.I).norm.pow 2)))
    (hi _ (continuous_const.mul hweight)) WeakH1.disk.isOpen.measurableSet
  intro z hz
  simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply]
  rw [groundFlux_product (hg1.differentiable (by norm_num) z)
      (hv.differentiable (by norm_num) z),
    groundFlux_product (hg1.differentiable (by norm_num) z)
      (hv.differentiable (by norm_num) z)]
  simp only [norm_mul, norm_pow, mul_pow]
  calc
    _ = ‖g z‖ ^ 2 * (‖g z‖ ^ 2 * gradSq v z) := by unfold gradSq; ring
    _ ≤ M * (‖g z‖ ^ 2 * gradSq v z) :=
      mul_le_mul_of_nonneg_right (hM z hz)
        (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
/-- Nonvanishing on the support makes the flux estimate available for
arbitrary smooth tests, including compactly supported interior tests. -/
theorem groundFlux_test_bound (g f : ℂ → ℂ) (V : ℂ → ℝ) (M : ℝ)
    (hg : ContDiff ℝ 2 g) (hf : ContDiff ℝ 1 f)
    (hr : ∀ z, (starRingEnd ℂ) (g z) = g z)
    (hb : ∀ z : Circle₁, g z = 0)
    (he : ∀ z ∈ (WeakH1.disk : Set ℂ), laplacian g z + V z * g z = 0)
    (hM : ∀ z ∈ (WeakH1.disk : Set ℂ), ‖g z‖ ^ 2 ≤ M)
    (hne : ∀ z ∈ tsupport f, g z ≠ 0) :
    (∫ z in (WeakH1.disk : Set ℂ),
      ‖groundFlux g f 1 z‖ ^ 2 + ‖groundFlux g f Complex.I z‖ ^ 2) ≤
      M * (∫ z in (WeakH1.disk : Set ℂ), gradSq f z - V z * ‖f z‖ ^ 2) := by
  have hv := contDiff_div_of_nonzero_on_tsupport hf (hg.of_le (by norm_num)) hne
  have h := groundFlux_multiple_bound g (fun z => f z / g z) V M hg hv hr hb he hM
  have hfg := mul_div_eq_of_nonzero_on_tsupport hne
  simpa only [hfg, congrFun hfg] using h

end KsIndex.GroundState
