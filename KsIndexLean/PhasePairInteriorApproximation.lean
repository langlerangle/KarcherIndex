module

public import KsIndexLean.PhasePairFiniteAssembly

@[expose] public section


open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace KsIndex.Trace
open KsIndex.WeakH1

/-- Smooth approximation of the actual interior remainder left by a finite
boundary partition. Its value identity reconstructs the original disk carrier. -/
theorem partition_interior_approximation {ι : Type*} (t : Finset ι)
    (ρ : ι → ℂ → ℝ) (u : ComplexH1) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    {H : Set ℂ} (hH : IsOpen H)
    (hu : ∀ᵐ z ∂volume.restrict (disk : Set ℂ), z ∈ H → valueCLM u z = 0)
    (hb : ∀ p : ℂ, ‖p‖ = 1 → p ∉ H →
      (fun z => ∑ i ∈ t, ρ i z) =ᶠ[𝓝 p] 1) :
    ∃ (u₀ : ComplexH1) (f₀ : ℂ → ℂ) (F₀ : ℕ → ℂ → ℂ) (U₀ : ℕ → ComplexH1),
      (valueCLM u₀ : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f₀ ∧
      (fun z => f₀ z + ∑ i ∈ t, ρ i z • valueCLM u z)
        =ᵐ[volume.restrict (disk : Set ℂ)] (valueCLM u : ℂ → ℂ) ∧
      Tendsto U₀ atTop (𝓝 u₀) ∧
      ∀ᶠ n in atTop, ContDiff ℝ ∞ (F₀ n) ∧ HasCompactSupport (F₀ n) ∧
        tsupport (F₀ n) ⊆ (disk : Set ℂ) ∧ RepresentsDiskJet (F₀ n) (U₀ n) := by
  obtain ⟨χ, hχ, hc, hs, he, _, _, _⟩ :=
    finite_weak_partition_values t ρ (fun _ => 1) u hρ hH hu hb
  obtain ⟨u₀, F₀, U₀, hF, hFc, ht, hv, hcoord⟩ :=
    interior_piece_carrier_tendsto hχ hc hs (carrier_hasJet u) (Lp.memLp (valueCLM u))
      (fun d => ((Lp.memLp (dxLp u)).const_smul d.re).add
        ((Lp.memLp (dyLp u)).const_smul d.im))
  refine ⟨u₀, (fun z => χ z • valueCLM u z), F₀, U₀, hv, ?_, ht, ?_⟩
  · filter_upwards [he, ae_restrict_mem KsIndex.SurfaceForm.measurableSet_disk] with z hz hzd
    simpa only [joined_value_on_disk u u 1 hzd] using hz
  · have hsc : tsupport (fun z => χ z • valueCLM u z) ⊆ (disk : Set ℂ) :=
      (tsupport_smul_subset_left χ _).trans hs
    filter_upwards [mollifier_support_open hc.smul_right disk.isOpen hsc] with n hn
    refine ⟨(hFc n).1, (hFc n).2, ?_, hcoord n⟩
    rwa [hF n]

end KsIndex.Trace
