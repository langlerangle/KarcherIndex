module

public import KsIndexLean.DNHalfTraceSpace

@[expose] public section


/-! Closed support for L2 classes means existence of a supported representative. -/
noncomputable section
open MeasureTheory Set
namespace KsIndex.CircleSobolev
open KsIndex.Trace

/-- A closed-support condition is independent of the chosen L2 representative.
The supported representative is obtained by setting values off the closed set to zero. -/
theorem exists_supported_representative_iff (A : Set Circle₁) (hA : IsClosed A)
    (f : Lp ℂ 2 circleMeasure) :
    (∃ g : Circle₁ → ℂ, f =ᵐ[circleMeasure] g ∧ tsupport g ⊆ A) ↔
      (f : Circle₁ → ℂ) =ᵐ[circleMeasure.restrict Aᶜ] 0 := by
  constructor
  · rintro ⟨g, hfg, hg⟩
    have he := hfg.filter_mono (ae_mono (Measure.restrict_le_self : circleMeasure.restrict Aᶜ ≤ circleMeasure))
    filter_upwards [he, ae_restrict_mem hA.isOpen_compl.measurableSet] with w hw hwa
    rw [hw]
    exact image_eq_zero_of_notMem_tsupport (fun hs => hwa (hg hs))
  · intro hf
    refine ⟨A.indicator f, ?_, ?_⟩
    · have he := (ae_restrict_iff' hA.isOpen_compl.measurableSet).mp hf
      filter_upwards [he] with w hw
      by_cases hwa : w ∈ A
      · simp [hwa]
      · rw [indicator_of_notMem hwa]
        exact hw hwa
    · exact closure_minimal support_indicator_subset hA

/-- Closed-support formulation for any nonnegative-order Sobolev realization. -/
theorem mem_arcZero_compl_iff_supported {s : ℝ} (hs : 0 ≤ s)
    (A : Set Circle₁) (hA : IsClosed A) (v : Space s) :
    v ∈ arcZero hs Aᶜ ↔
      ∃ g : Circle₁ → ℂ, toL2 hs v =ᵐ[circleMeasure] g ∧ tsupport g ⊆ A := by
  rw [mem_arcZero_iff, exists_supported_representative_iff A hA]

/-- The complement of the Dirichlet arc is the closed nonnegative-real-power set. -/
lemma boundaryArc_zero_compl (k : ℕ) :
    (boundaryArc k 0)ᶜ = {w : Circle₁ | 0 ≤ ((w : ℂ) ^ k).re} := by
  ext w
  simp only [mem_compl_iff, mem_boundaryArc, pow_zero, one_mul, mem_ofPred_eq, not_lt]

lemma isClosed_boundaryArc_zero_compl (k : ℕ) : IsClosed ((boundaryArc k 0)ᶜ) := by
  rw [boundaryArc_zero_compl]
  exact isClosed_le continuous_const (by fun_prop)

/-- DN membership has an actual representative supported in the closed allowed set. -/
theorem mem_dnSpace_iff_supported_compl (k : ℕ) (v : Space (1 / 2 : ℝ)) :
    v ∈ dnSpace k ↔ ∃ g : Circle₁ → ℂ,
      toL2 (show (0 : ℝ) ≤ 1 / 2 by norm_num) v =ᵐ[circleMeasure] g ∧
        tsupport g ⊆ (boundaryArc k 0)ᶜ := by
  have h := mem_arcZero_compl_iff_supported (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    ((boundaryArc k 0)ᶜ) (isClosed_boundaryArc_zero_compl k) v
  simpa only [compl_compl, dnSpace] using h

end KsIndex.CircleSobolev
