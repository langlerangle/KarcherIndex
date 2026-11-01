module

public import KsIndexLean.ChartH1Carrier
public import KsIndexLean.SigmaDeriv

@[expose] public section


open Set MeasureTheory
noncomputable section
namespace KsIndex.Spherical

lemma sigma_preimage_null {s : Set ℂ} (hs : volume s = 0) :
    volume (Bracket.σ ⁻¹' s) = 0 := by
  have hd : DifferentiableOn ℝ Bracket.σ (s \ {0}) := by
    intro z hz
    have h := SigmaDeriv.hasFDerivAt_sigmaR (by simpa using hz.2)
    exact h.differentiableAt.differentiableWithinAt
  have hi : volume (Bracket.σ '' (s \ {0})) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd
      (measure_mono_null sdiff_subset hs)
  apply measure_mono_null (t := Bracket.σ '' (s \ {0}) ∪ {0})
  · intro z hz
    by_cases h0 : z = 0
    · exact Or.inr h0
    · apply Or.inl
      refine ⟨Bracket.σ z, ⟨hz, ?_⟩, Bracket.σ_σ z⟩
      simpa [Bracket.σ] using h0
  · exact measure_union_null hi (measure_singleton 0)

lemma ae_comp_sigma {P : ℂ → Prop} (h : ∀ᵐ z ∂volume, P z) :
    ∀ᵐ z ∂volume, P (Bracket.σ z) := by
  rw [ae_iff] at h ⊢
  exact sigma_preimage_null h

end KsIndex.Spherical
