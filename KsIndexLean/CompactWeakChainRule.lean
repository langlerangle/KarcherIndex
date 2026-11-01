module

public import KsIndexLean.LipschitzL2Composition

@[expose] public section


open Set MeasureTheory Filter Topology
noncomputable section
namespace KsIndex.Trace

/-- Actual nonlinear weak directional chain rule for compact whole-space L2 weak data.
The derivative field is supplied with its classical derivative identity, continuity and bound. -/
theorem compact_weakLine_chain_rule {F : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℂ}
    {C : NNReal} (hF : LipschitzWith C F) (h0 : F 0 = 0)
    (hD : Continuous D) (hd : ∀ w, HasFDerivAt F (D w) w)
    {B : ℝ} (hbound : ∀ w, ‖D w‖ ≤ B)
    {u v : ℂ → ℂ} {d : ℂ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hw : TauCeti.HasWeakLineDerivOn volume ⊤ u v d) :
    TauCeti.HasWeakLineDerivOn volume ⊤ (F ∘ u) (fun z => D (u z) (v z)) d := by
  let us := fun n => compactMollify (shrinkingMollifier n) u
  let vs := fun n => compactMollify (shrinkingMollifier n) v
  have hum n : MemLp (us n) 2 volume := compactMollify_memLp _ hu huc
  have hvm n : MemLp (vs n) 2 volume := compactMollify_memLp _ hv hvc
  have hut : Tendsto (fun n => (hum n).toLp (us n)) atTop (𝓝 (hu.toLp u)) :=
    compactMollify_tendsto shrinkingMollifier_radius hu huc
  have hvt : Tendsto (fun n => (hvm n).toLp (vs n)) atTop (𝓝 (hv.toLp v)) :=
    compactMollify_tendsto shrinkingMollifier_radius hv hvc
  obtain ⟨ns, hns, hae⟩ := exists_ae_subsequence_of_toLp_tendsto hum hu hut
  have hAm n : AEStronglyMeasurable (fun z => D (us (ns n) z)) volume :=
    hD.comp_aestronglyMeasurable (hum (ns n)).aestronglyMeasurable
  have hBm : AEStronglyMeasurable (fun z => D (u z)) volume :=
    hD.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hAb n : ∀ᵐ z ∂volume, ‖D (us (ns n) z)‖ ≤ B :=
    Eventually.of_forall fun z => hbound _
  have hBb : ∀ᵐ z ∂volume, ‖D (u z)‖ ≤ B := Eventually.of_forall fun z => hbound _
  have hAt : ∀ᵐ z ∂volume, Tendsto (fun n => D (us (ns n) z)) atTop (𝓝 (D (u z))) := by
    filter_upwards [hae] with z hz
    exact (hD.tendsto (u z)).comp hz
  have hval := lipschitz_toLp_tendsto hF h0 (fun n => hum (ns n)) hu
    (hut.comp hns.tendsto_atTop)
  have hjet := bounded_operator_tendsto hAm hBm (fun n => hvm (ns n)) hv hAb hBb hAt
    (hvt.comp hns.tendsto_atTop)
  have hwm n : TauCeti.HasWeakLineDerivOn volume ⊤ (F ∘ us (ns n))
      (fun z => D (us (ns n) z) (vs (ns n) z)) d := by
    apply TauCeti.hasWeakLineDerivOn_of_hasLineDerivAt
      (((hF.comp_memLp h0 (hum (ns n))).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
      (((bounded_operator_memLp (hAm n) (hvm (ns n)) (hAb n)).locallyIntegrable
        (by norm_num)).locallyIntegrableOn _)
    intro z _
    exact hasLineDerivAt_nonlinear_comp (hd _) (compactMollify_hasLineDerivAt _ hw z)
  exact weakLine_of_tendsto_toLp d (fun n => hF.comp_memLp h0 (hum (ns n)))
    (fun n => bounded_operator_memLp (hAm n) (hvm (ns n)) (hAb n))
    (hF.comp_memLp h0 hu) (bounded_operator_memLp hBm hv hBb) hwm hval hjet

/-- The compact full weak Frechet chain rule, obtained direction by direction. -/
theorem compact_weakF_chain_rule {F : ℂ → ℂ} {D : ℂ → ℂ →L[ℝ] ℂ}
    {C : NNReal} (hF : LipschitzWith C F) (h0 : F 0 = 0)
    (hD : Continuous D) (hd : ∀ w, HasFDerivAt F (D w) w)
    {B : ℝ} (hbound : ∀ w, ‖D w‖ ≤ B)
    {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 volume) (hU : ∀ d, MemLp (fun z => U z d) 2 volume)
    (huc : HasCompactSupport u) (hUc : ∀ d, HasCompactSupport (fun z => U z d))
    (hw : TauCeti.HasWeakFDerivOn volume ⊤ u U) :
    TauCeti.HasWeakFDerivOn volume ⊤ (F ∘ u) (fun z => (D (u z)).comp (U z)) := by
  rw [TauCeti.hasWeakFDerivOn_iff]
  intro d
  exact compact_weakLine_chain_rule hF h0 hD hd hbound hu (hU d) huc (hUc d)
    (hw.hasWeakLineDerivOn d)

end KsIndex.Trace
