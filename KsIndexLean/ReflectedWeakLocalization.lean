module

public import KsIndexLean.ReflectionLocalization
public import KsIndexLean.SeamDomainWeakGluing

@[expose] public section


open Set MeasureTheory TopologicalSpace
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket

/-- Supported symmetric localization of an actual reflected weak disk function gives a
whole-plane weak H1 function with both value and full product-jet parity. -/
theorem reflected_weak_localization {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (s : ℂ) (hsign : s ^ 2 = 1)
    (hm : arcTrace A u = s • arcTrace A u) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ))
    (hi : ∀ z, χ (σ z) = χ z) :
    let v := fun z => χ z • joinedDiskValue u u s z
    let J := fun z => χ z • joinedDiskJet u u s z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u u s z)
    TauCeti.HasWeakFDerivOn volume ⊤ v J ∧ MemLp v 2 volume ∧
      (∀ d, MemLp (fun z => J z d) 2 volume) ∧
      (∀ᵐ z ∂volume, s • v (σ z) = v z) ∧
      (∀ᵐ z ∂volume, s • (J (σ z)).comp (fderiv ℝ σ z) = J z) := by
  dsimp only
  have hL d : MemLp (fun z => joinedDiskJet u u s z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA u u s).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  obtain ⟨hw, hv, hJ⟩ := weakH1_localization hχ hc hs (seamDomain_weak_gluing hA u u s hm)
    (seamDomain_value_memLp hA u u s) hL
  exact ⟨hw, hv, hJ, localized_value_parity hi s (joined_self_value_parity u s hsign),
    localized_jet_parity hχ hi s (joined_self_value_parity u s hsign)
      (joined_self_jet_parity u s hsign)⟩

end KsIndex.Trace
