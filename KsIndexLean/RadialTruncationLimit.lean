module

public import KsIndexLean.RadialTruncationJet

@[expose] public section


open Set MeasureTheory Filter Topology TopologicalSpace
noncomputable section
namespace KsIndex.Trace

lemma radialWeight_tendsto (z : ℂ) :
    Tendsto (fun t : ℝ => radialWeight t z) (𝓝 0) (𝓝 1) := by
  have h : Continuous (fun t : ℝ => Real.sqrt (1 + t * ‖z‖ ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_id.mul continuous_const))
  have hi := h.continuousAt.inv₀ (by norm_num : Real.sqrt (1 + (0 : ℝ) * ‖z‖ ^ 2) ≠ 0)
  change Tendsto (fun t : ℝ => (Real.sqrt (1 + t * ‖z‖ ^ 2))⁻¹) (𝓝 0)
    (𝓝 ((Real.sqrt (1 + (0 : ℝ) * ‖z‖ ^ 2))⁻¹)) at hi
  simp only [zero_mul, add_zero, Real.sqrt_one, inv_one] at hi
  exact hi

lemma radialTruncate_tendsto (z : ℂ) :
    Tendsto (fun t : ℝ => radialTruncate t z) (𝓝 0) (𝓝 z) := by
  have h := (radialWeight_tendsto z).smul_const z
  simp only [one_smul] at h
  exact h

lemma radialJet_tendsto (z : ℂ) :
    Tendsto (fun t : ℝ => radialJet t z) (𝓝 0) (𝓝 (ContinuousLinearMap.id ℝ ℂ)) := by
  have hs : Tendsto (fun t : ℝ => Real.sqrt (1 + t * ‖z‖ ^ 2)) (𝓝 0) (𝓝 1) := by
    have h : Continuous (fun t : ℝ => Real.sqrt (1 + t * ‖z‖ ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.add (continuous_id.mul continuous_const))
    simpa only [zero_mul, add_zero, Real.sqrt_one] using h.tendsto 0
  have hc : Tendsto (fun t : ℝ => -(t / Real.sqrt (1 + t * ‖z‖ ^ 2) ^ 3))
      (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.div (hs.pow 3) (by norm_num)).neg
  have hw : Tendsto (fun t : ℝ => radialWeightJet t z) (𝓝 0) (𝓝 0) := by
    have h := hc.smul_const (innerSL ℝ z)
    simp only [zero_smul] at h
    exact h
  have hr : Tendsto (fun t : ℝ => (radialWeightJet t z).smulRight z) (𝓝 0) (𝓝 0) := by
    have h := (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := ℂ) (F := ℂ)).continuous.tendsto
      (0, z) |>.comp (hw.prodMk_nhds tendsto_const_nhds)
    have hz : (0 : ℂ →L[ℝ] ℝ).smulRight z = 0 := by
      ext w
      simp
    change Tendsto (fun t => (radialWeightJet t z).smulRight z) (𝓝 0)
      (𝓝 ((0 : ℂ →L[ℝ] ℝ).smulRight z)) at h
    rw [hz] at h
    exact h
  have h := ((radialWeight_tendsto z).smul_const (ContinuousLinearMap.id ℝ ℂ)).add hr
  simp only [one_smul, add_zero] at h
  exact h

/-- The radial maps satisfy the actual open-domain weak chain rule. -/
theorem weakH1_radialTruncate {Ω : Opens ℂ} {t : ℝ} (ht : 0 ≤ t)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hU : ∀ d, MemLp (fun z => U z d) 2 (volume.restrict (Ω : Set ℂ)))
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U) :
    TauCeti.HasWeakFDerivOn volume Ω (radialTruncate t ∘ u)
      (fun z => (radialJet t (u z)).comp (U z)) :=
  weakH1_chain_rule (radialTruncate_lipschitz ht) (radialTruncate_zero t)
    (radialJet_continuous ht) (radialTruncate_hasFDerivAt ht) (radialJet_norm_le ht) hu hU hw

end KsIndex.Trace
