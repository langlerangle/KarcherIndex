module

public import KsIndexLean.WeakCutoffValueLimit

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma cutoff_weighted_lp_integrable (k j : ℕ) (f : L2C) :
    IntegrableOn (fun z => (1 - cutP k (cutoffEps j) z) ^ 2 * ‖f z‖ ^ 2) disk := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp
    (Lp.memLp f)
  have hc := (cutP_contDiff k (cutoffEps_pos j) (cutoffEps_lt_one j)).continuous
  apply hi.mono' (((continuous_const.sub hc).pow 2).aestronglyMeasurable.mul
    hi.aestronglyMeasurable)
  filter_upwards [] with z
  change ‖(1 - cutP k (cutoffEps j) z) ^ 2 * ‖f z‖ ^ 2‖ ≤ ‖f z‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (cutoff_error_sq_le_one k j z)

lemma cutoff_coordinate_error_le (k j : ℕ) (f g : L2C) (u : ℂ → ℂ) (e : ℂ)
    (he : ∀ z, ‖fderiv ℝ (cutP k (cutoffEps j)) z e‖ ^ 2 ≤
      Surface.gradSq (cutPC k (cutoffEps j)) z)
    (hfg : (g : ℂ → ℂ) =ᵐ[volume.restrict disk] (fun z =>
      cutP k (cutoffEps j) z • f z + fderiv ℝ (cutP k (cutoffEps j)) z e • u z))
    (hi : IntegrableOn (fun z => ‖u z‖ ^ 2 * Surface.gradSq (cutPC k (cutoffEps j)) z) disk) :
    ‖g - f‖ ^ 2 ≤ 2 * (∫ z in disk, (1 - cutP k (cutoffEps j) z) ^ 2 * ‖f z‖ ^ 2) +
      2 * ∫ z in disk, ‖u z‖ ^ 2 * Surface.gradSq (cutPC k (cutoffEps j)) z := by
  have hf := cutoff_weighted_lp_integrable k j f
  rw [lp_norm_sq, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hf.const_mul 2) (hi.const_mul 2)]
  apply integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp (g - f)).aestronglyMeasurable).mp
      (Lp.memLp (g - f))) ((hf.const_mul 2).add (hi.const_mul 2))
  filter_upwards [Lp.coeFn_sub g f, hfg] with z hs hz
  change ‖(g - f) z‖ ^ 2 ≤ _
  rw [hs]
  change ‖g z - f z‖ ^ 2 ≤ _
  rw [hz]
  have hid : cutP k (cutoffEps j) z • f z +
      fderiv ℝ (cutP k (cutoffEps j)) z e • u z - f z =
      (cutP k (cutoffEps j) z - 1) • f z +
      fderiv ℝ (cutP k (cutoffEps j)) z e • u z := by module
  rw [hid]
  have hn (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h := norm_add_le a b
    have hsq := pow_le_pow_left₀ (norm_nonneg (a + b)) h 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  apply (hn _ _).trans
  rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs]
  have h := mul_le_mul_of_nonneg_right (he z) (sq_nonneg ‖u z‖)
  dsimp only [Pi.add_apply]
  nlinarith

lemma cutoff_coordinate_tendsto {k : ℕ} (hk : 1 ≤ k) (f : L2C) (g : ℕ → L2C)
    (u : ℂ → ℂ) (e : ℂ) {M : ℝ}
    (he : ∀ j z, ‖fderiv ℝ (cutP k (cutoffEps j)) z e‖ ^ 2 ≤
      Surface.gradSq (cutPC k (cutoffEps j)) z)
    (hfg : ∀ j, (g j : ℂ → ℂ) =ᵐ[volume.restrict disk] (fun z =>
      cutP k (cutoffEps j) z • f z + fderiv ℝ (cutP k (cutoffEps j)) z e • u z))
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖u z‖ ≤ M)
    (hm : AEStronglyMeasurable u (volume.restrict disk)) :
    Tendsto g atTop (𝓝 f) := by
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp
    (Lp.memLp f)
  have hsum := ((cutoff_weighted_error_tendsto_zero hk hf).const_mul 2).add
    ((bounded_cutoff_gradient_error_tendsto_zero k hu hm).const_mul 2)
  have hsq : Tendsto (fun j => ‖g j - f‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => sq_nonneg _) (fun j =>
      cutoff_coordinate_error_le k j f (g j) u e (he j) (hfg j)
        (bounded_cutoff_gradient_error_integrable k j hm hu))
    simp only [mul_zero, add_zero] at hsum
    exact hsum
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hsq

end KsIndex.Trace
