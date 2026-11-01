module

public import KsIndexLean.PhasePairSupport
public import KsIndexLean.MollifiedReflectionDerivative
public import KsIndexLean.CollarJetLimit

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- The inverse-side mollifier converges with its actual derivatives on the
fixed collar. Multiplication by the constant inverse phase can be applied
subsequently; no reflection parity hypothesis is needed. -/
theorem inverse_mollification_collar {u : ℂ → ℂ} {J : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 volume) (hJ : ∀ d, MemLp (fun z => J z d) 2 volume)
    (hc : HasCompactSupport u) (hcJ : ∀ d, HasCompactSupport (fun z => J z d))
    (hw : TauCeti.HasWeakFDerivOn volume ⊤ u J) :
    let μ := volume.restrict (annulusSet (1 / 2 : ℝ) 2)
    ∃ (hv : MemLp (u ∘ σ) 2 μ)
      (hD : ∀ d, MemLp (fun z => (J (σ z)).comp (fderiv ℝ σ z) d) 2 μ)
      (fv : ℕ → Lp ℂ 2 μ) (fD : ℕ → ℂ → Lp ℂ 2 μ),
      (∀ n, (fv n : ℂ → ℂ) =ᵐ[μ]
        (compactMollify (shrinkingMollifier n) u) ∘ σ) ∧
      (∀ n d, (fD n d : ℂ → ℂ) =ᵐ[μ]
        fun z => fderiv ℝ ((compactMollify (shrinkingMollifier n) u) ∘ σ) z d) ∧
      Tendsto fv atTop (𝓝 (hv.toLp (u ∘ σ))) ∧
      ∀ d, Tendsto (fun n => fD n d) atTop
        (𝓝 ((hD d).toLp (fun z => (J (σ z)).comp (fderiv ℝ σ z) d))) := by
  let μ := volume.restrict (annulusSet (1 / 2 : ℝ) 2)
  let g := fun n => compactMollify (shrinkingMollifier n) u
  let X := fun n => compactMollify (shrinkingMollifier n) (fun z => J z 1)
  let Y := fun n => compactMollify (shrinkingMollifier n) (fun z => J z Complex.I)
  have hg n : MemLp (g n) 2 volume := compactMollify_memLp _ hu hc
  have hX n : MemLp (X n) 2 volume := compactMollify_memLp _ (hJ 1) (hcJ 1)
  have hY n : MemLp (Y n) 2 volume := compactMollify_memLp _ (hJ Complex.I) (hcJ Complex.I)
  have hgr n : MemLp (g n) 2 μ := (hg n).mono_measure Measure.restrict_le_self
  have hXr n : MemLp (X n) 2 μ := (hX n).mono_measure Measure.restrict_le_self
  have hYr n : MemLp (Y n) 2 μ := (hY n).mono_measure Measure.restrict_le_self
  have hur : MemLp u 2 μ := hu.mono_measure Measure.restrict_le_self
  have hUr : MemLp (fun z => J z 1) 2 μ := (hJ 1).mono_measure Measure.restrict_le_self
  have hVr : MemLp (fun z => J z Complex.I) 2 μ :=
    (hJ Complex.I).mono_measure Measure.restrict_le_self
  have hjet d : sigmaJetPullback (fun z => J z 1) (fun z => J z Complex.I) d =
      (fun z => (J (σ z)).comp (fderiv ℝ σ z) d) :=
    funext (sigmaJetPullback_eq J d)
  have hD d : MemLp (fun z => (J (σ z)).comp (fderiv ℝ σ z) d) 2 μ := by
    simpa only [hjet] using sigmaJetPullback_memLp hUr hVr d
  refine ⟨memLp_sigma_collar hur, hD,
    fun n => (memLp_sigma_collar (hgr n)).toLp (g n ∘ σ),
    fun n d => (sigmaJetPullback_memLp (hXr n) (hYr n) d).toLp
      (sigmaJetPullback (X n) (Y n) d),
    fun n => (memLp_sigma_collar (hgr n)).coeFn_toLp, ?_, ?_, ?_⟩
  · intro n d
    filter_upwards [(sigmaJetPullback_memLp (hXr n) (hYr n) d).coeFn_toLp,
      ae_restrict_mem measurableSet_annulusSet] with z hz hzc
    rw [hz, fderiv_comp_sigma (norm_pos_iff.mp (lt_trans (by norm_num) hzc.1))
      ((compactMollify_smooth _ hu).differentiable (by norm_num) _)]
    congr 2
    · exact (funext (compactMollify_fderiv _ hu hw 1)).symm
    · exact (funext (compactMollify_fderiv _ hu hw Complex.I)).symm
  · exact toLp_sigma_collar_tendsto hgr hur
      (toLp_mono_measure_tendsto Measure.restrict_le_self hg hu
        (compactMollify_tendsto shrinkingMollifier_radius hu hc))
  · intro d
    have htX := toLp_mono_measure_tendsto (ν := μ) Measure.restrict_le_self hX (hJ 1)
      (compactMollify_tendsto shrinkingMollifier_radius (hJ 1) (hcJ 1))
    have htY := toLp_mono_measure_tendsto (ν := μ) Measure.restrict_le_self hY (hJ Complex.I)
      (compactMollify_tendsto shrinkingMollifier_radius (hJ Complex.I) (hcJ Complex.I))
    simpa only [hjet] using
      sigmaJetPullback_tendsto hXr hYr hUr hVr htX htY d

/-- Apply inverse-side collar convergence to the localized two-disk join.
The weak jet is derived from the actual matching traces, rather than supplied
as an additional analytic assumption. -/
theorem localized_phase_pair_inverse_collar {A : Set Circle₁} (hA : IsOpen A)
    (u v : KsIndex.WeakH1.ComplexH1) (c : ℂ)
    (hm : arcTrace A u = c • arcTrace A v) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) :
    let w := fun z => χ z • joinedDiskValue u v c z
    let W := fun z => χ z • joinedDiskJet u v c z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u v c z)
    let μ := volume.restrict (annulusSet (1 / 2 : ℝ) 2)
    ∃ (hv : MemLp (w ∘ σ) 2 μ)
      (hD : ∀ d, MemLp (fun z => (W (σ z)).comp (fderiv ℝ σ z) d) 2 μ)
      (fv : ℕ → Lp ℂ 2 μ) (fD : ℕ → ℂ → Lp ℂ 2 μ),
      (∀ n, (fv n : ℂ → ℂ) =ᵐ[μ]
        (compactMollify (shrinkingMollifier n) w) ∘ σ) ∧
      (∀ n d, (fD n d : ℂ → ℂ) =ᵐ[μ]
        fun z => fderiv ℝ ((compactMollify (shrinkingMollifier n) w) ∘ σ) z d) ∧
      Tendsto fv atTop (𝓝 (hv.toLp (w ∘ σ))) ∧
      ∀ d, Tendsto (fun n => fD n d) atTop
        (𝓝 ((hD d).toLp (fun z => (W (σ z)).comp (fderiv ℝ σ z) d))) := by
  have hL d : MemLp (fun z => joinedDiskJet u v c z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA u v c).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  obtain ⟨hw, hv, hW⟩ := weakH1_localization
    (u := joinedDiskValue u v c) (U := joinedDiskJet u v c) hχ hc hs
    (seamDomain_weak_gluing hA u v c hm) (seamDomain_value_memLp hA u v c) hL
  exact inverse_mollification_collar
    (u := fun z => χ z • joinedDiskValue u v c z)
    (J := fun z => χ z • joinedDiskJet u v c z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u v c z))
    hv hW hc.smul_right
    (localized_jet_compact hc _ _) hw

end KsIndex.Trace
