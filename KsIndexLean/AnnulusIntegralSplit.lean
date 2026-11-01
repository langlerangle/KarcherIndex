module

public import KsIndexLean.JoinedJetUniqueness
public import KsIndexLean.SeamInversionTransport

@[expose] public section


/-! Splitting the collar integral across its null middle circle. -/
noncomputable section
open Set MeasureTheory
namespace KsIndex.Trace

lemma annulus_ae_halves :
    annulusSet (1 / 2 : ℝ) 2 =ᵐ[volume] innerHalfAnnulus ∪ outerHalfAnnulus := by
  filter_upwards [ae_norm_ne_one] with z hz
  apply propext
  change (1 / 2 < ‖z‖ ∧ ‖z‖ < 2) ↔
    (1 / 2 < ‖z‖ ∧ ‖z‖ < 1) ∨ (1 < ‖z‖ ∧ ‖z‖ < 2)
  constructor
  · intro h
    rcases lt_or_gt_of_ne hz with hn | hn
    · exact Or.inl ⟨h.1, hn⟩
    · exact Or.inr ⟨hn, h.2⟩
  · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]

lemma integral_annulus_split {F : ℂ → ℂ}
    (hF : IntegrableOn F (annulusSet (1 / 2 : ℝ) 2)) :
    (∫ z in annulusSet (1 / 2 : ℝ) 2, F z) =
      (∫ z in innerHalfAnnulus, F z) + ∫ z in outerHalfAnnulus, F z := by
  rw [setIntegral_congr_set annulus_ae_halves]
  apply setIntegral_union
  · exact Set.disjoint_left.mpr (fun z hi ho => (not_lt_of_ge hi.2.le) ho.1)
  · exact measurableSet_annulusSet
  · exact hF.mono_set (fun z hz => ⟨hz.1, lt_trans hz.2 (by norm_num)⟩)
  · exact hF.mono_set (fun z hz => ⟨lt_trans (by norm_num) hz.1, hz.2⟩)

lemma integral_split_of_annular_support {F : ℂ → ℂ}
    (hF : IntegrableOn F (annulusSet (1 / 2 : ℝ) 2))
    (hs : ∀ z, z ∉ annulusSet (1 / 2 : ℝ) 2 → F z = 0) :
    (∫ z, F z) = (∫ z in innerHalfAnnulus, F z) + ∫ z in outerHalfAnnulus, F z := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  exact integral_annulus_split hF

end KsIndex.Trace
