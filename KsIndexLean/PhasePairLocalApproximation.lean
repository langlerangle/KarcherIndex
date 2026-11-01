module

public import KsIndexLean.PhasePairLowerH1

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1 KsIndex.Bracket KsIndex.SingleDisk

/-- The explicit inverse-phase pair also has the exact reverse germ. -/
lemma phaseGerm_restricted_pair_reverse (c : ℂ) (hc : c ≠ 0) (F : ℂ → ℂ) :
    phaseGerm c⁻¹ (closedDiskRestriction (fun z => c⁻¹ * F (σ z)))
      (closedDiskRestriction F) = (fun z => c⁻¹ * F (σ z)) := by
  have h := phaseGerm_restricted_pair c⁻¹ (inv_ne_zero hc) (fun z => c⁻¹ * F (σ z))
  simpa only [inv_inv, σ_σ, ← mul_assoc, mul_inv_cancel₀ hc, one_mul] using h

/-- A smooth representative supplies the value and both derivative coordinates
of a disk H1 carrier. This does not impose any seam point-value normalization. -/
def RepresentsDiskJet (f : ℂ → ℂ) (u : ComplexH1) : Prop :=
  (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f ∧
  (dxLp u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ f z 1) ∧
  (dyLp u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] (fun z => fderiv ℝ f z Complex.I)

/-- Local two-sided phase-compatible smoothing in the actual product H1
space. Eventually, both representatives are smooth and supported in the prescribed
seam collar. Their phase germ is exactly the upper mollifier at every scale. -/
theorem localized_phase_pair_h1 {A : Set Circle₁} (hA : IsOpen A)
    (u v : ComplexH1) (c : ℂ) (hc0 : c ≠ 0) (hm : arcTrace A u = c • arcTrace A v)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (seamDomain A hA : Set ℂ)) (hi : ∀ z, χ (σ z) = χ z) :
    let f := fun n => compactMollify (shrinkingMollifier n)
      (fun z => χ z • joinedDiskValue u v c z)
    let g := fun n z => c⁻¹ * f n (σ z)
    ∃ (uχ vχ : ComplexH1) (U V : ℕ → ComplexH1),
      Tendsto (fun n => (U n, V n)) atTop (𝓝 (uχ, vχ)) ∧
      (valueCLM uχ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • valueCLM u z) ∧
      (valueCLM vχ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)]
        (fun z => χ z • valueCLM v z) ∧
      (∀ n, phaseGerm c (closedDiskRestriction (f n)) (closedDiskRestriction (g n)) = f n) ∧
      ∀ᶠ n in atTop,
        RepresentsDiskJet (f n) (U n) ∧ RepresentsDiskJet (g n) (V n) ∧
        ContDiff ℝ ∞ (f n) ∧ ContDiff ℝ ∞ (g n) ∧
        HasCompactSupport (f n) ∧ HasCompactSupport (g n) ∧
        tsupport (f n) ⊆ seamDomain A hA ∧ tsupport (g n) ⊆ seamDomain A hA := by
  obtain ⟨uχ, U, htU, huχ, hU⟩ := localized_pair_upper_h1 hA u v c hm hχ hc hs
  obtain ⟨vχ, V, htV, hvχ, hV⟩ := localized_pair_lower_h1 hA u v c hc0 hm hχ hc hs hi
  have hL d : MemLp (fun z => joinedDiskJet u v c z d) 2
      (volume.restrict (seamDomain A hA : Set ℂ)) :=
    (seamDomain_jet_memLp hA u v c).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℂ d)
  have hw := (weakH1_localization hχ hc hs (seamDomain_weak_gluing hA u v c hm)
    (seamDomain_value_memLp hA u v c) hL).2.1
  have hws : tsupport (fun z => χ z • joinedDiskValue u v c z) ⊆ seamDomain A hA :=
    (tsupport_smul_subset_left χ _).trans hs
  refine ⟨uχ, vχ, U, V, htU.prodMk_nhds htV, huχ, hvχ,
    fun n => phaseGerm_restricted_pair c hc0 _, ?_⟩
  filter_upwards [hV, phase_pair_mollification_support hA c⁻¹ hw hc.smul_right hws]
    with n hv hn
  exact ⟨hU n, hv, compactMollify_smooth _ hw, hn.2.2.2,
    compactMollify_support _ hc.smul_right, hn.2.2.1, hn.1, hn.2.1⟩

end KsIndex.Trace
