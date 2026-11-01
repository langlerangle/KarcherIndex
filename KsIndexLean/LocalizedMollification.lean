module

public import KsIndexLean.CompactWeakMollification

@[expose] public section


open Set MeasureTheory Filter Topology TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

lemma localized_jet_compact {χ : ℂ → ℝ} (hc : HasCompactSupport χ)
    (u : ℂ → ℂ) (U : ℂ → ℂ →L[ℝ] ℂ) (d : ℂ) :
    HasCompactSupport (fun z => (χ z • U z + (fderiv ℝ χ z).smulRight (u z)) d) := by
  have h1 : HasCompactSupport (fun z => χ z • U z d) := hc.smul_right
  have h2 : HasCompactSupport (fun z => fderiv ℝ χ z d • u z) :=
    (hc.fderiv_apply (𝕜 := ℝ) d).smul_right
  exact h1.add h2

/-- Supported localization admits actual smooth convolutions whose values and every
classical directional derivative converge in global L2. -/
theorem localized_mollification {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U)
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hU : ∀ d, MemLp (fun z => U z d) 2 (volume.restrict (Ω : Set ℂ)))
    {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) :
    let v := fun z => χ z • u z
    let V := fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)
    ∃ (hv : MemLp v 2 volume) (hV : ∀ d, MemLp (fun z => V z d) 2 volume)
      (fv : ℕ → Lp ℂ 2 (volume : Measure ℂ))
      (fV : ℕ → ℂ → Lp ℂ 2 (volume : Measure ℂ)),
      (∀ n, ContDiff ℝ ∞ (compactMollify (φ n) v)) ∧
      (∀ n, (fv n : ℂ → ℂ) =ᵐ[volume] compactMollify (φ n) v) ∧
      (∀ n d, (fV n d : ℂ → ℂ) =ᵐ[volume]
        fun z => lineDeriv ℝ (compactMollify (φ n) v) z d) ∧
      Tendsto fv atTop (𝓝 (hv.toLp v)) ∧
      ∀ d, Tendsto (fun n => fV n d) atTop (𝓝 ((hV d).toLp (fun z => V z d))) := by
  dsimp only
  obtain ⟨hw', hv, hV⟩ := weakH1_localization hχ hc hs hw hu hU
  have hvc : HasCompactSupport (fun z => χ z • u z) := hc.smul_right
  let fv := fun n => (compactMollify_memLp (φ n) hv hvc).toLp _
  let fV := fun n d => (compactMollify_memLp (φ n) (hV d)
    (localized_jet_compact hc u U d)).toLp _
  refine ⟨hv, hV, fv, fV, fun n => compactMollify_smooth (φ n) hv,
    fun n => (compactMollify_memLp (φ n) hv hvc).coeFn_toLp, ?_,
    compactMollify_tendsto hφ hv hvc, ?_⟩
  · intro n d
    filter_upwards [(compactMollify_memLp (φ n) (hV d)
      (localized_jet_compact hc u U d)).coeFn_toLp] with z hz
    exact hz.trans (compactMollify_hasLineDerivAt (φ n)
      (hw'.hasWeakLineDerivOn d) z).lineDeriv.symm
  · intro d
    exact compactMollify_tendsto hφ (hV d) (localized_jet_compact hc u U d)

/-- A concrete family of normalized mollifier kernels with shrinking outer radii. -/
def shrinkingMollifier (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

lemma shrinkingMollifier_radius :
    Tendsto (fun n => (shrinkingMollifier n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

end KsIndex.Trace
