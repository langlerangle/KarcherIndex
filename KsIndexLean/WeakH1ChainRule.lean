module

public import KsIndexLean.CompactWeakChainRule

@[expose] public section


open Set MeasureTheory Filter Topology TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

/-- Nonlinear weak Frechet chain rule on an arbitrary open planar domain with L2 data.
The nonlinear map fixes zero, is Lipschitz, and has a continuous bounded actual derivative. -/
theorem weakH1_chain_rule {Ω : Opens ℂ} {F : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℂ}
    {C : NNReal} (hF : LipschitzWith C F) (h0 : F 0 = 0)
    (hD : Continuous D) (hd : ∀ w, HasFDerivAt F (D w) w)
    {B : ℝ} (hbound : ∀ w, ‖D w‖ ≤ B)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hU : ∀ d, MemLp (fun z => U z d) 2 (volume.restrict (Ω : Set ℂ)))
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U) :
    TauCeti.HasWeakFDerivOn volume Ω (F ∘ u) (fun z => (D (u z)).comp (U z)) := by
  have hDm : AEStronglyMeasurable (fun z => D (u z)) (volume.restrict (Ω : Set ℂ)) :=
    hD.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hDb : ∀ᵐ z ∂volume.restrict (Ω : Set ℂ), ‖D (u z)‖ ≤ B :=
    Eventually.of_forall fun z => hbound _
  apply weakF_of_local
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hF.comp_memLp h0 hu).locallyIntegrable (by norm_num))
  · intro d
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((bounded_operator_memLp hDm (hU d) hDb).locallyIntegrable (by norm_num))
  · intro z hz
    obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hz)
    let χ : ContDiffBump z := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    have hχ : ContDiff ℝ ∞ (χ : ℂ → ℝ) := χ.contDiff
    have hs : tsupport (χ : ℂ → ℝ) ⊆ (Ω : Set ℂ) := by
      rw [χ.tsupport_eq]
      exact hrs
    obtain ⟨hw', hu', hU'⟩ := weakH1_localization hχ χ.hasCompactSupport hs hw hu hU
    have huc : HasCompactSupport (fun w => χ w • u w) := χ.hasCompactSupport.smul_right
    have hw'' := compact_weakF_chain_rule hF h0 hD hd hbound hu' hU' huc
      (localized_jet_compact χ.hasCompactSupport u U) hw'
    let V : Opens ℂ := ⟨Metric.ball z χ.rIn, Metric.isOpen_ball⟩
    refine ⟨V, Metric.mem_ball_self χ.rIn_pos, ?_⟩
    have hone (w : ℂ) (hw : w ∈ V) : χ w = 1 :=
      χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hw)
    have hzero (w : ℂ) (hw : w ∈ V) : fderiv ℝ (χ : ℂ → ℝ) w = 0 := by
      rw [(χ.eventuallyEq_one_of_mem_ball hw).fderiv_eq]
      simp
    apply ((hw''.mono (show V ≤ ⊤ from le_top)).congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with w hw
      simp only [Function.comp_apply, hone w hw, one_smul]
    · filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with w hw
      simp [hone w hw, hzero w hw]

end KsIndex.Trace
