module

public import KsIndexLean.PhasePairH1Convergence

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- The inverse-phase component of the SAME mollified join converges in disk
H1 to the localized lower function. Its smooth representatives retain the
actual inverse-phase formula, so they can be paired with the upper sequence. -/
theorem localized_pair_lower_h1 {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hc0 : c ≠ 0) (hm : arcTrace A u = c • arcTrace A v)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) (hi : ∀ z, χ (σ z) = χ z) :
    let f := fun n z => c⁻¹ • compactMollify (shrinkingMollifier n)
      (fun z => χ z • joinedDiskValue u v c z) (σ z)
    ∃ (vχ : ComplexH1) (V : ℕ → ComplexH1), Tendsto V atTop (𝓝 vχ) ∧
      (valueCLM vχ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • valueCLM v z) ∧
      ∀ᶠ n in atTop,
        (valueCLM (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f n ∧
        (dxLp (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (f n) z 1) ∧
        (dyLp (V n) : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
          (fun z => fderiv ℝ (f n) z Complex.I) := by
  let w := fun z => χ z • joinedDiskValue u v c z
  let g := fun z => χ z • joinedDiskValue v u c⁻¹ z
  let J := fun z => χ z • joinedDiskJet v u c⁻¹ z +
    (fderiv ℝ χ z).smulRight (joinedDiskValue v u c⁻¹ z)
  have hm' : arcTrace A v = c⁻¹ • arcTrace A u := by
    rw [hm, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hL (a b : ComplexH1) (s d : ℂ) : MemLp (fun z => joinedDiskJet a b s z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA a b s).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  obtain ⟨hgw, hg, hJ⟩ := weakH1_localization hχ hc hs
    (seamDomain_weak_gluing hA v u c⁻¹ hm') (seamDomain_value_memLp hA v u c⁻¹) (hL v u c⁻¹)
  obtain ⟨vχ, hvχ, hxχ, hyχ⟩ := carrier_of_weakJet (hgw.mono le_top)
    (hg.mono_measure Measure.restrict_le_self)
    (fun d => (hJ d).mono_measure Measure.restrict_le_self)
  obtain ⟨hv, hD, fv, fD, hfv, hfD, htv, htD⟩ :=
    localized_phase_pair_inverse_collar hA u v c hm hχ hc hs
  have hw : MemLp w 2 volume := (weakH1_localization hχ hc hs
    (seamDomain_weak_gluing hA u v c hm) (seamDomain_value_memLp hA u v c) (hL u v c)).2.1
  have hws : tsupport w ⊆ (seamDomain A hA : Set ℂ) :=
    (tsupport_smul_subset_left χ _).trans hs
  have hsupport := phase_pair_mollification_support hA c⁻¹ hw hc.smul_right hws
  have hsm : ∀ᶠ n in atTop,
      ContDiff ℝ ∞ (fun z => c⁻¹ • compactMollify (shrinkingMollifier n) w (σ z)) ∧
      HasCompactSupport (fun z => c⁻¹ • compactMollify (shrinkingMollifier n) w (σ z)) ∧
      tsupport (fun z => c⁻¹ • compactMollify (shrinkingMollifier n) w (σ z)) ⊆
        annulusSet (1 / 2 : ℝ) 2 := by
    filter_upwards [hsupport] with n hn
    exact ⟨hn.2.2.2, hn.2.2.1, fun z hz => (hn.2.1 hz).1⟩
  have hnot z (hz : ‖z‖ ≤ 1 / 2) : z ∉ tsupport χ :=
    fun h => (not_lt.mpr hz) (hs h).1.1
  have hg0 z (hz : ‖z‖ ≤ 1 / 2) : g z = 0 := by
    simp [g, image_eq_zero_of_notMem_tsupport (hnot z hz)]
  have hJ0 z (hz : ‖z‖ ≤ 1 / 2) (d : ℂ) : J z d = 0 := by
    simp [J, image_eq_zero_of_notMem_tsupport (hnot z hz),
      fderiv_apply_eq_zero_of_notMem_tsupport (hnot z hz) d]
  have hvlim : (↑(c⁻¹ • hv.toLp _) : ℂ → ℂ) =ᵐ[
      volume.restrict (annulusSet (1 / 2 : ℝ) 2)] g := by
    filter_upwards [Lp.coeFn_smul c⁻¹ (hv.toLp _), hv.coeFn_toLp,
      (localized_pair_value_inverse_phase u v hc0 hi).filter_mono
        (ae_mono Measure.restrict_le_self)] with z ha hb he
    exact (ha.trans (congrArg (fun x : ℂ => c⁻¹ • x) hb)).trans he
  have hDlim d : (↑(c⁻¹ • (hD d).toLp _) : ℂ → ℂ) =ᵐ[
      volume.restrict (annulusSet (1 / 2 : ℝ) 2)] (fun z => J z d) := by
    filter_upwards [Lp.coeFn_smul c⁻¹ ((hD d).toLp _), (hD d).coeFn_toLp,
      (localized_pair_jet_inverse_phase u v hc0 hχ hi).filter_mono
        (ae_mono Measure.restrict_le_self)] with z ha hb he
    exact (ha.trans (congrArg (fun x : ℂ => c⁻¹ • x) hb)).trans
      (congrArg (fun L : ℂ →L[ℝ] ℂ => L d) he)
  have hfval n : (↑(c⁻¹ • fv n) : ℂ → ℂ) =ᵐ[
      volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
      (fun z => c⁻¹ • compactMollify (shrinkingMollifier n) w (σ z)) := by
    filter_upwards [Lp.coeFn_smul c⁻¹ (fv n), hfv n] with z ha hb
    exact ha.trans (congrArg (fun x : ℂ => c⁻¹ • x) hb)
  have hfder n d : (↑(c⁻¹ • fD n d) : ℂ → ℂ) =ᵐ[
      volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
      (fun z => fderiv ℝ (fun z => c⁻¹ • compactMollify (shrinkingMollifier n) w (σ z)) z d) := by
    filter_upwards [Lp.coeFn_smul c⁻¹ (fD n d), hfD n d] with z ha hb
    rw [ha, Pi.smul_apply, hb]
    exact (congrArg (fun F : ℂ → ℂ →L[ℝ] ℂ => F z d)
      (fderiv_const_smul_field (𝕜 := ℝ) (f := compactMollify (shrinkingMollifier n) w ∘ σ) c⁻¹)).symm
  obtain ⟨V, ht, hV⟩ := smooth_collar_carrier_tendsto vχ hvχ hxχ hyχ hsm hg0 hJ0
    (c⁻¹ • hv.toLp _) (fun d => c⁻¹ • (hD d).toLp _)
    (fun n => c⁻¹ • fv n) (fun n d => c⁻¹ • fD n d)
    hvlim hDlim hfval hfder (htv.const_smul c⁻¹) (fun d => (htD d).const_smul c⁻¹)
  refine ⟨vχ, V, ht, ?_, hV⟩
  filter_upwards [hvχ, ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hz hzd
  rw [hz, joined_value_on_disk v u c⁻¹ hzd]

end KsIndex.Trace
