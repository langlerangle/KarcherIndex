module

public import KsIndexLean.ArcLocalAgreement

@[expose] public section


open Set MeasureTheory
open scoped ContDiff

namespace KsIndex.Trace
open KsIndex.WeakH1

lemma continuous_neighbourhood_of_smooth_germ {f : ℂ → ℂ} {x : ℂ}
    (hf : ContDiffAt ℝ ∞ f x) :
    ∃ O : Set ℂ, IsOpen O ∧ x ∈ O ∧ ContinuousOn f O := by
  have h0 : ContDiffAt ℝ 0 f x := hf.of_le (by simp)
  have hc : ∀ᶠ z in nhds x, ContinuousAt f z :=
    (h0.eventually (by simp)).mono (fun _ hz => hz.continuousAt)
  obtain ⟨O, hOc, hO, hx⟩ := mem_nhds_iff.mp hc
  exact ⟨O, hO, hx, fun z hz => (hOc hz).continuousWithinAt⟩

/-- A smooth boundary germ representing the interior class determines its trace on an arc. -/
theorem diskTrace_smooth_germs (u : ComplexH1) {A : Set Circle₁} {f : ℂ → ℂ}
    (hf : ∀ w ∈ A, ContDiffAt ℝ ∞ f (w : ℂ))
    (he : (valueCLM u : ℂ → ℂ) =ᵐ[volume.restrict (disk : Set ℂ)] f) :
    (diskTraceCLM u : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict A] (fun w => f (w : ℂ)) := by
  apply diskTrace_local_agreement u
  intro w hw
  obtain ⟨O, hO, hwO, hc⟩ := continuous_neighbourhood_of_smooth_germ (hf w hw)
  exact ⟨O, hO, hwO, hc, he.mono (fun _ hz _ => hz)⟩

end KsIndex.Trace
