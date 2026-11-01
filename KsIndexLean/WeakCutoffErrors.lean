module

public import KsIndexLean.CutoffLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace
open KsIndex.Surface KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma cutoff_log_scale (j : ℕ) : Lε (cutoffEps j) = (j : ℝ) + 1 := by
  simp [Lε, cutoffEps]

lemma cutoff_energy_tendsto_zero (k : ℕ) :
    Tendsto (fun j => ∫ z in disk, gradSq (cutPC k (cutoffEps j)) z) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => integral_nonneg (fun z => by unfold gradSq; positivity))
    (fun j => (energy_cutP_le k (cutoffEps_pos j) (cutoffEps_lt_one j)).trans_eq
      (by rw [cutoff_log_scale]))
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_const_div_atTop_nhds_zero_nat
      (4 * Real.pi * (pF k).card ^ 2 * Mψ ^ 2 : ℝ)).comp (tendsto_add_atTop_nat 1)

lemma cutoff_error_sq_le_one (k j : ℕ) (z : ℂ) :
    (1 - cutP k (cutoffEps j) z) ^ 2 ≤ 1 := by
  have h0 := cutP_nonneg k (cutoffEps j) z
  have h1 := cutP_le_one k (cutoffEps j) z
  nlinarith

/-- Dominated convergence for any integrable weak value or derivative energy density. -/
lemma cutoff_weighted_error_tendsto_zero {k : ℕ} (hk : 1 ≤ k) {g : ℂ → ℝ}
    (hg : IntegrableOn g disk) :
    Tendsto (fun j => ∫ z in disk, (1 - cutP k (cutoffEps j) z) ^ 2 * g z)
      atTop (𝓝 0) := by
  have hm (j : ℕ) : AEStronglyMeasurable
      (fun z => (1 - cutP k (cutoffEps j) z) ^ 2 * g z) (volume.restrict disk) :=
    (((continuous_const.sub (cutP_contDiff k (cutoffEps_pos j)
      (cutoffEps_lt_one j)).continuous).pow 2).aestronglyMeasurable).mul hg.aestronglyMeasurable
  have hb (j : ℕ) : ∀ᵐ z ∂volume.restrict disk,
      ‖(1 - cutP k (cutoffEps j) z) ^ 2 * g z‖ ≤ ‖g z‖ := by
    apply Filter.Eventually.of_forall
    intro z
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_error_sq_le_one k j z)
  have hl : ∀ᵐ z ∂volume.restrict disk,
      Tendsto (fun j => (1 - cutP k (cutoffEps j) z) ^ 2 * g z) atTop (𝓝 (0 : ℝ)) := by
    apply ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
    intro z hz
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (cutP_tendsto_one hk hz)).pow 2).mul_const (g z)
  simpa using tendsto_integral_of_dominated_convergence (fun z => ‖g z‖) hm hg.norm hb hl

lemma bounded_cutoff_gradient_error_integrable (k j : ℕ) {u : ℂ → ℂ} {M : ℝ}
    (hm : AEStronglyMeasurable u (volume.restrict disk))
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖u z‖ ≤ M) :
    IntegrableOn (fun z => ‖u z‖ ^ 2 * gradSq (cutPC k (cutoffEps j)) z) disk := by
  have hi := (integrable_gradSq_cutPC k (cutoffEps_pos j)
    (cutoffEps_lt_one j)).restrict (s := disk)
  apply (hi.const_mul (M ^ 2)).mono' ((hm.norm.pow 2).mul hi.aestronglyMeasurable)
  filter_upwards [hu] with z hz
  have hn : 0 ≤ ‖u z‖ ^ 2 * gradSq (cutPC k (cutoffEps j)) z := by
    unfold gradSq
    positivity
  change ‖‖u z‖ ^ 2 * gradSq (cutPC k (cutoffEps j)) z‖ ≤
    M ^ 2 * gradSq (cutPC k (cutoffEps j)) z
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  apply mul_le_mul_of_nonneg_right _ (by unfold gradSq; positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) hz 2

/-- For bounded values the extra product-rule density is controlled by cutoff energy.
The boundedness assumption must be removed by truncation before claiming arbitrary H1 density. -/
lemma bounded_cutoff_gradient_error_le (k j : ℕ) {u : ℂ → ℂ} {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖u z‖ ≤ M)
    (hi : IntegrableOn (fun z => ‖u z‖ ^ 2 * gradSq (cutPC k (cutoffEps j)) z) disk) :
    (∫ z in disk, ‖u z‖ ^ 2 * gradSq (cutPC k (cutoffEps j)) z) ≤
      M ^ 2 * ∫ z in disk, gradSq (cutPC k (cutoffEps j)) z := by
  rw [← integral_const_mul]
  apply integral_mono_ae hi
    ((integrable_gradSq_cutPC k (cutoffEps_pos j) (cutoffEps_lt_one j)).restrict.const_mul _)
  filter_upwards [hu] with z hz
  apply mul_le_mul_of_nonneg_right _ (by unfold gradSq; positivity)
  exact pow_le_pow_left₀ (norm_nonneg _) hz 2

lemma bounded_cutoff_gradient_error_tendsto_zero (k : ℕ) {u : ℂ → ℂ} {M : ℝ}
    (hu : ∀ᵐ z ∂volume.restrict disk, ‖u z‖ ≤ M)
    (hm : AEStronglyMeasurable u (volume.restrict disk)) :
    Tendsto (fun j => ∫ z in disk, ‖u z‖ ^ 2 * gradSq (cutPC k (cutoffEps j)) z)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun j => integral_nonneg (fun z => by unfold gradSq; positivity))
    (fun j => bounded_cutoff_gradient_error_le k j hu
      (bounded_cutoff_gradient_error_integrable k j hm hu))
  simpa using (cutoff_energy_tendsto_zero k).const_mul (M ^ 2)

end KsIndex.Trace
