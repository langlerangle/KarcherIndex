module

public import KsIndexLean.WeakCutoffErrors
public import KsIndexLean.WeakH1Adapter

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped Gradient ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.PunctureCutoff KsIndex.FaithfulInjection

lemma cutoff_multiplier_bound (k j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧
    (∀ z ∈ disk, |cutP k (cutoffEps j) z| ≤ M) ∧
    (∀ z ∈ disk, ‖∇ (cutP k (cutoffEps j)) z‖ ≤ M) := by
  have hc := (cutP_contDiff k (cutoffEps_pos j) (cutoffEps_lt_one j)).continuous_fderiv
    (by norm_num)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), ?_, ?_⟩
  · intro z hz
    rw [abs_of_nonneg (cutP_nonneg k (cutoffEps j) z)]
    exact (cutP_le_one k (cutoffEps j) z).trans (le_max_left _ _)
  · intro z hz
    change ‖(InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ (cutP k (cutoffEps j)) z)‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (hC z (Metric.ball_subset_closedBall hz)).trans (le_max_right _ _)

/-- Multiplication by the actual puncture cutoff in the adopted complex weak H1 carrier. -/
def diskCutoff (k j : ℕ) : ComplexH1 →L[ℂ] ComplexH1 :=
  let h := cutoff_multiplier_bound k j
  smoothMulCLM (cutP k (cutoffEps j)) (cutP_contDiff k (cutoffEps_pos j) (cutoffEps_lt_one j))
    h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2

lemma diskCutoff_value_ae (k j : ℕ) (u : ComplexH1) :
    (valueCLM (diskCutoff k j u) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun z => cutP k (cutoffEps j) z • valueCLM u z) := by
  have h := cutoff_multiplier_bound k j
  have hm := smoothMul_value_ae (cutP k (cutoffEps j))
    (cutP_contDiff k (cutoffEps_pos j) (cutoffEps_lt_one j))
    h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2 u
  filter_upwards [valueLp_ae (diskCutoff k j u), hm, valueLp_ae u] with z hz hm hu
  exact hz.trans (hm.trans (congrArg (fun w : ℂ => cutP k (cutoffEps j) z • w) hu.symm))

lemma diskCutoff_jet_ae (k j : ℕ) (u : ComplexH1) :
    Dxy (dxLp (diskCutoff k j u)) (dyLp (diskCutoff k j u)) =ᵐ[volume.restrict disk]
      (fun z => cutP k (cutoffEps j) z • Dxy (dxLp u) (dyLp u) z +
        (fderiv ℝ (cutP k (cutoffEps j)) z).smulRight (valueCLM u z)) := by
  have h := cutoff_multiplier_bound k j
  have hm := smoothMul_weakDerivative_ae (cutP k (cutoffEps j))
    (cutP_contDiff k (cutoffEps_pos j) (cutoffEps_lt_one j))
    h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2 u
  filter_upwards [weakDerivative_coordinates (diskCutoff k j u), hm,
    weakDerivative_coordinates u, valueLp_ae u] with z hz hm hu hv
  exact hz.symm.trans (hm.trans (by rw [hu, ← hv]; rfl))

lemma diskCutoff_dx_ae (k j : ℕ) (u : ComplexH1) :
    (dxLp (diskCutoff k j u) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun z => cutP k (cutoffEps j) z • dxLp u z +
        fderiv ℝ (cutP k (cutoffEps j)) z 1 • valueCLM u z) := by
  filter_upwards [diskCutoff_jet_ae k j u] with z hz
  simpa only [Dxy_one, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply] using congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hz

lemma diskCutoff_dy_ae (k j : ℕ) (u : ComplexH1) :
    (dyLp (diskCutoff k j u) : ℂ → ℂ) =ᵐ[volume.restrict disk]
      (fun z => cutP k (cutoffEps j) z • dyLp u z +
        fderiv ℝ (cutP k (cutoffEps j)) z Complex.I • valueCLM u z) := by
  filter_upwards [diskCutoff_jet_ae k j u] with z hz
  simpa only [Dxy_I, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply] using congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) hz

end KsIndex.Trace
