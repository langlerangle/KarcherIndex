module

public import KsIndexLean.MollifiedReflectionDerivative

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.SingleDisk KsIndex.WeakH1

/-- Explicit reflected mollifications approximate a compact weak function and its actual
weak derivatives on the collar. Exact reflected smoothness is imposed on every approximant. -/
theorem reflected_mollification (s : ℂ) (hs : s ^ 2 = 1) {u : ℂ → ℂ}
    {J : ℂ → ℂ →L[ℝ] ℂ} (hu : MemLp u 2 volume)
    (hJ : ∀ d, MemLp (fun z => J z d) 2 volume)
    (hc : HasCompactSupport u) (hcJ : ∀ d, HasCompactSupport (fun z => J z d))
    (hw : TauCeti.HasWeakFDerivOn volume ⊤ u J)
    (hp : ∀ᵐ z ∂volume, s • u (σ z) = u z)
    (hpJ : ∀ᵐ z ∂volume, s • (J (σ z)).comp (fderiv ℝ σ z) = J z) :
    ∃ (fv : ℕ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
      (fD : ℕ → ℂ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))),
      (∀ n z, z ≠ 0 → ContDiffAt ℝ ∞
        (refl s (closedDiskRestriction
          (reflectionAverage s (compactMollify (shrinkingMollifier n) u)))) z) ∧
      (∀ n, (fv n : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
        reflectionAverage s (compactMollify (shrinkingMollifier n) u)) ∧
      (∀ n d, (fD n d : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
        fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n) u)) z d) ∧
      Tendsto fv atTop (𝓝 ((hu.mono_measure Measure.restrict_le_self).toLp u)) ∧
      ∀ d, Tendsto (fun n => fD n d) atTop
        (𝓝 (((hJ d).mono_measure Measure.restrict_le_self).toLp (fun z => J z d))) := by
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
  have hval n := reflectionAverage_memLp s (hgr n)
  have hder n d := reflectionAverageJet_memLp s (hXr n) (hYr n) d
  let fv := fun n => (hval n).toLp (reflectionAverage s (g n))
  let fD := fun n d => (hder n d).toLp (reflectionAverageJet s (X n) (Y n) d)
  refine ⟨fv, fD, ?_, fun n => (hval n).coeFn_toLp, ?_, ?_, ?_⟩
  · intro n z hz
    exact refl_average_contDiffAt s hs hz (compactMollify_smooth _ hu).contDiffAt
      (compactMollify_smooth _ hu).contDiffAt
  · intro n d
    filter_upwards [(hder n d).coeFn_toLp, ae_restrict_mem measurableSet_annulusSet]
      with z hz hzc
    rw [hz]
    exact (compactMollify_reflection_fderiv _ s hu hw d
      (norm_pos_iff.mp (lt_trans (by norm_num) hzc.1))).symm
  · apply reflectionAverage_tendsto_fixed s hgr hur
    · exact toLp_mono_measure_tendsto Measure.restrict_le_self hg hu
        (compactMollify_tendsto shrinkingMollifier_radius hu hc)
    · exact hp.filter_mono (ae_mono Measure.restrict_le_self)
  · intro d
    have htX : Tendsto (fun n => (hXr n).toLp (X n)) atTop
        (𝓝 (hUr.toLp (fun z => J z 1))) :=
      toLp_mono_measure_tendsto Measure.restrict_le_self hX (hJ 1)
        (compactMollify_tendsto shrinkingMollifier_radius (hJ 1) (hcJ 1))
    have htY : Tendsto (fun n => (hYr n).toLp (Y n)) atTop
        (𝓝 (hVr.toLp (fun z => J z Complex.I))) :=
      toLp_mono_measure_tendsto Measure.restrict_le_self hY (hJ Complex.I)
        (compactMollify_tendsto shrinkingMollifier_radius (hJ Complex.I) (hcJ Complex.I))
    have hpar : ∀ᵐ z ∂μ,
        s * sigmaJetPullback (fun w => J w 1) (fun w => J w Complex.I) d z =
          Dxy (fun w => J w 1) (fun w => J w Complex.I) z d := by
      filter_upwards [hpJ.filter_mono (ae_mono Measure.restrict_le_self)] with z hz
      rw [Dxy_apply, ← realLinear_coordinates, sigmaJetPullback_eq]
      exact congrArg (fun L : ℂ →L[ℝ] ℂ => L d) hz
    have hh := reflectionAverageJet_tendsto_fixed s hXr hYr hUr hVr htX htY d hpar
    have he : (fun z => Dxy (fun w => J w 1) (fun w => J w Complex.I) z d) =
        (fun z => J z d) := funext fun z => (realLinear_coordinates (J z) d).symm
    simp only [he] at hh
    exact hh

end KsIndex.Trace
