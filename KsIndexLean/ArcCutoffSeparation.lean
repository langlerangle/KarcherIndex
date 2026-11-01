module

public import KsIndexLean.SeamCutoff
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section


open Set MeasureTheory
open scoped ContDiff Topology

noncomputable section
namespace KsIndex.Trace

lemma ae_eq_on_nonzero_of_circleMul_eq (η : C(Circle₁, ℝ))
    {F G : Lp ℂ 2 circleMeasure} (h : circleMul η F = circleMul η G) :
    F =ᵐ[circleMeasure.restrict {w | η w ≠ 0}] G := by
  have he : ∀ᵐ w ∂circleMeasure, η w • F w = η w • G w := by
    have hf := circleMul_coe η F
    rw [h] at hf
    exact hf.symm.trans (circleMul_coe η G)
  apply (ae_restrict_iff'
    (isClosed_eq η.continuous continuous_const).isOpen_compl.measurableSet).mpr
  filter_upwards [he] with w hw hn
  have hc := congrArg (fun z : ℂ => (η w)⁻¹ • z) hw
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hc

/-- Smooth supported multipliers separate the genuine L² classes on an open arc. -/
theorem boundaryRestrict_eq_of_cutoff_tests {A : Set Circle₁} (hA : IsOpen A)
    {F G : Lp ℂ 2 circleMeasure}
    (h : ∀ (η : ℂ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η),
      (∀ w : Circle₁, w ∉ A → η w = 0) →
      circleMul (realCircleMap η hη.continuous) F =
        circleMul (realCircleMap η hη.continuous) G) :
    boundaryRestrict A F = boundaryRestrict A G := by
  classical
  choose η hη hs hn using fun w : A => exists_seam_cutoff hA w.property
  let U : A → Set Circle₁ := fun w => {x | η w x ≠ 0}
  have ho : ∀ w, IsOpen (U w) := fun w =>
    (isClosed_eq ((hη w).continuous.comp continuous_subtype_val) continuous_const).isOpen_compl
  have hc : A ⊆ ⋃ w, U w := by
    intro w hw
    refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
    have he : η ⟨w, hw⟩ (w : ℂ) = 1 := (hn ⟨w, hw⟩).eq_of_nhds
    change η ⟨w, hw⟩ (w : ℂ) ≠ 0
    rw [he]
    norm_num
  obtain ⟨s, hsc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof A).elim_countable_subcover U ho hc
  have he : F =ᵐ[circleMeasure.restrict (⋃ w ∈ s, U w)] G := by
    apply (ae_eq_restrict_biUnion_iff U hsc F G).mpr
    intro w _
    exact ae_eq_on_nonzero_of_circleMul_eq _ (h (η w) (hη w) (hs w))
  have heA := he.filter_mono (ae_mono (Measure.restrict_mono hcover le_rfl))
  exact Lp.ext ((boundaryRestrict_coe_ae A F).trans (heA.trans (boundaryRestrict_coe_ae A G).symm))

end KsIndex.Trace
