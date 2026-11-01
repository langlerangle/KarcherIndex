module

public import KsIndexLean.SmoothGermTrace

@[expose] public section


/-! Weak traces are determined by smooth local extensions from the closed
side of the disk. The extensions may vary with the boundary point. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace KsIndex.Trace
open KsIndex.WeakH1

theorem diskTrace_closed_side_germs (u : ComplexH1) {A : Set Circle₁} {f : ℂ → ℂ}
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f)
    (hf : ∀ w ∈ A, ∃ F : ℂ → ℂ, ContDiffAt ℝ ∞ F (w : ℂ) ∧
      ∀ᶠ z in 𝓝 (w : ℂ), ‖z‖ ≤ 1 → f z = F z) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] (fun w => f w) := by
  apply ae_on_of_local_neighbourhoods
  intro x hx
  obtain ⟨F, hF, hs⟩ := hf x hx
  obtain ⟨O, hO, hxO, hFc⟩ := continuous_neighbourhood_of_smooth_germ hF
  obtain ⟨V, hVs, hV, hxV⟩ := eventually_nhds_iff.mp hs
  have hlocal : ∀ᵐ z ∂volume.restrict (disk : Set ℂ),
      z ∈ O ∩ V → valueCLM u z = F z := by
    filter_upwards [he, ae_restrict_mem disk.isOpen.measurableSet] with z hz hd hzOV
    have hn : ‖z‖ < 1 := by
      have hd' : z ∈ Metric.ball (0 : ℂ) 1 := hd
      simpa only [Metric.mem_ball, dist_zero_right] using hd'
    exact hz.trans (hVs z hzOV.2 hn.le)
  obtain ⟨B, hB, hxB, ht⟩ := exists_boundary_neighbourhood_agreement u
    (hO.inter hV) (hFc.mono inter_subset_left) ⟨hxO, hxV⟩ hlocal
  let D : Set Circle₁ := B ∩ (Subtype.val ⁻¹' V)
  have hD : IsOpen D := hB.inter (hV.preimage continuous_subtype_val)
  refine ⟨D, hD, ⟨hxB, hxV⟩, ?_⟩
  have htD := ht.filter_mono (ae_mono (Measure.restrict_mono
    (show D ⊆ B from inter_subset_left) le_rfl))
  filter_upwards [htD, ae_restrict_mem hD.measurableSet] with w hw hwD
  exact hw.trans (hVs w hwD.2 (mem_sphere_zero_iff_norm.mp w.property).le).symm

end KsIndex.Trace
