module

public import KsIndexLean.PhasePairMollification

@[expose] public section


open Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket

/-- Inverting a compactly supported collar function preserves compact support;
the scalar phase does not enlarge it. -/
lemma phasePullback_tsupport (a : ℂ) {F : ℂ → ℂ} (hc : HasCompactSupport F)
    (h0 : (0 : ℂ) ∉ tsupport F) :
    tsupport (fun z => a * F (σ z)) ⊆ σ '' tsupport F := by
  apply closure_minimal _ (sigma_tsupport_compact hc h0).isClosed
  intro z hz
  refine ⟨σ z, ?_, σ_σ z⟩
  by_contra hn
  apply hz
  simp [image_eq_zero_of_notMem_tsupport hn]

/-- Both smooth representatives of a localized phase pair stay in the same
seam collar, and both are globally smooth, including at the disk center. -/
theorem phase_pair_mollification_support {A : Set Circle₁} (hA : IsOpen A)
    (a : ℂ) {w : ℂ → ℂ} (hw : MemLp w 2 volume) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ seamDomain A hA) :
    ∀ᶠ n in atTop,
      tsupport (compactMollify (shrinkingMollifier n) w) ⊆ seamDomain A hA ∧
      tsupport (fun z => a * compactMollify (shrinkingMollifier n) w (σ z)) ⊆
        seamDomain A hA ∧
      HasCompactSupport (fun z => a * compactMollify (shrinkingMollifier n) w (σ z)) ∧
      ContDiff ℝ ∞ (fun z => a * compactMollify (shrinkingMollifier n) w (σ z)) := by
  filter_upwards [mollifier_support_open hc (seamDomain A hA).isOpen hs] with n hn
  have h0 : (0 : ℂ) ∉ tsupport (compactMollify (shrinkingMollifier n) w) :=
    fun h => zero_notMem_seamDomain hA (hn h)
  have hcF := compactMollify_support (shrinkingMollifier n) hc
  have hp := phasePullback_tsupport a hcF h0
  have hsub : tsupport (fun z => a * compactMollify (shrinkingMollifier n) w (σ z)) ⊆
      seamDomain A hA := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hp hz
    exact seamDomain_sigma hA (hn hy)
  refine ⟨hn, hsub, (sigma_tsupport_compact hcF h0).of_isClosed_subset
    isClosed_closure hp, ?_⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have he : (fun z => a * compactMollify (shrinkingMollifier n) w (σ z))
        =ᶠ[𝓝 (0 : ℂ)] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => zero_notMem_seamDomain hA (hsub h))
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact contDiffAt_const.mul
      ((compactMollify_smooth (shrinkingMollifier n) hw).contDiffAt.comp z (contDiffAt_σ hz))

end KsIndex.Trace
