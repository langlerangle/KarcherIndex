module

public import KsIndexLean.ReflectedMollification
public import KsIndexLean.ReflectedWeakLocalization

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.Bracket KsIndex.SingleDisk KsIndex.WeakH1

/-- Apply the explicit smoothing construction to a supported symmetric localization of
an actual weak disk function. The cutoff is assumed here; its construction is separate. -/
theorem localized_reflected_approximation {A : Set Circle₁} (hA : IsOpen A)
    (u : ComplexH1) (s : ℂ) (hsign : s ^ 2 = 1)
    (hm : arcTrace A u = s • arcTrace A u) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ))
    (hi : ∀ z, χ (σ z) = χ z) :
    let v := fun z => χ z • joinedDiskValue u u s z
    let W := fun z => χ z • joinedDiskJet u u s z +
      (fderiv ℝ χ z).smulRight (joinedDiskValue u u s z)
    ∃ (hv : MemLp v 2 volume) (hW : ∀ d, MemLp (fun z => W z d) 2 volume),
    ∃ (fv : ℕ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2)))
      (fD : ℕ → ℂ → Lp ℂ 2 (volume.restrict (annulusSet (1 / 2 : ℝ) 2))),
      (∀ n z, z ≠ 0 → ContDiffAt ℝ ∞
        (refl s (closedDiskRestriction
          (reflectionAverage s (compactMollify (shrinkingMollifier n) v)))) z) ∧
      (∀ n, (fv n : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
        reflectionAverage s (compactMollify (shrinkingMollifier n) v)) ∧
      (∀ n d, (fD n d : ℂ → ℂ) =ᵐ[volume.restrict (annulusSet (1 / 2 : ℝ) 2)]
        fun z => fderiv ℝ (reflectionAverage s (compactMollify (shrinkingMollifier n) v)) z d) ∧
      Tendsto fv atTop (𝓝 ((hv.mono_measure Measure.restrict_le_self).toLp v)) ∧
      ∀ d, Tendsto (fun n => fD n d) atTop
        (𝓝 (((hW d).mono_measure Measure.restrict_le_self).toLp (fun z => W z d))) := by
  dsimp only
  obtain ⟨hw, hv, hW, hp, hpW⟩ := reflected_weak_localization hA u s hsign hm hχ hc hs hi
  refine ⟨hv, hW, ?_⟩
  exact reflected_mollification s hsign hv hW hc.smul_right
    (localized_jet_compact hc (joinedDiskValue u u s) (joinedDiskJet u u s)) hw hp hpW

end KsIndex.Trace
