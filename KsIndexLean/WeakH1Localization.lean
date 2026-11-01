module

public import KsIndexLean.SupportedLocalIntegrability
public import KsIndexLean.WeakH1Adapter

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace

lemma memLp_smooth_product_jet_whole {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hU : ∀ d, MemLp (fun z => U z d) 2 (volume.restrict (Ω : Set ℂ))) (d : ℂ) :
    MemLp (fun z => (χ z • U z + (fderiv ℝ χ z).smulRight (u z)) d) 2 volume := by
  have h1 := memLp_continuous_mul_supported hχ.continuous hc hs (hU d)
  have hd : Continuous (fun z => fderiv ℝ χ z d) :=
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 := memLp_continuous_mul_supported hd (hc.fderiv_apply (𝕜 := ℝ) d)
    ((tsupport_fderiv_apply_subset ℝ d).trans hs) hu
  exact h1.add h2

/-- Compact localization supplies both genuine whole-space weak differentiation and
L2 control of the value and every derivative direction. -/
theorem weakH1_localization {Ω : Opens ℂ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (Ω : Set ℂ)) {u : ℂ → ℂ} {U : ℂ → ℂ →L[ℝ] ℂ}
    (hw : TauCeti.HasWeakFDerivOn volume Ω u U)
    (hu : MemLp u 2 (volume.restrict (Ω : Set ℂ)))
    (hU : ∀ d, MemLp (fun z => U z d) 2 (volume.restrict (Ω : Set ℂ))) :
    TauCeti.HasWeakFDerivOn volume ⊤ (fun z => χ z • u z)
        (fun z => χ z • U z + (fderiv ℝ χ z).smulRight (u z)) ∧
      MemLp (fun z => χ z • u z) 2 volume ∧
      ∀ d, MemLp (fun z => (χ z • U z + (fderiv ℝ χ z).smulRight (u z)) d) 2 volume :=
  ⟨weakF_smooth_mul_whole hχ hs hw, memLp_continuous_mul_supported hχ.continuous hc hs hu,
    memLp_smooth_product_jet_whole hχ hc hs hu hU⟩

open KsIndex.WeakH1

/-- The localization theorem applies to every function in the adopted disk H1 carrier. -/
theorem diskH1_localization (u : ComplexH1) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (disk : Set ℂ)) :
    TauCeti.HasWeakFDerivOn volume ⊤ (fun z => χ z • valueCLM u z)
        (fun z => χ z • Dxy (dxLp u) (dyLp u) z +
          (fderiv ℝ χ z).smulRight (valueCLM u z)) ∧
      MemLp (fun z => χ z • valueCLM u z) 2 volume ∧
      ∀ d, MemLp (fun z => (χ z • Dxy (dxLp u) (dyLp u) z +
        (fderiv ℝ χ z).smulRight (valueCLM u z)) d) 2 volume := by
  apply weakH1_localization hχ hc hs (carrier_hasJet u) (Lp.memLp (valueCLM u))
  intro d
  exact ((Lp.memLp (dxLp u)).const_smul d.re).add ((Lp.memLp (dyLp u)).const_smul d.im)

end KsIndex.Trace
