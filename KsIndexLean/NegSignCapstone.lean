module

public import KsIndexLean.ProdAssembly
public import KsIndexLean.AlphaRemarkTrialNormalization

@[expose] public section


/-! The negative spectral sign at the lower test point.
The certified production bound `qform_le_grand` places the circle form of the
concrete trial strictly below zero at `spectralLower`; the variational
characterization then forces the least eigenvalue below zero. -/

noncomputable section
namespace KsIndex.NegSignProd
open CircleQ Statements KsIndex.AlphaRemarkTrial

theorem trial_ne_zero : trial ≠ 0 := by
  intro h
  exact trial_head_ne_zero (by simp [h])

/-- The negative spectral sign: `γ(spectralLower) < 0`, on the certified
production bound. First hypothesis of `decimal_enclosure_of_signs`. -/
theorem gam_spectralLower_neg : gam KsIndex.AlphaRemark.spectralLower < 0 := by
  have hpos : 0 < normSq trial := normSq_pos trial_memDom trial_ne_zero
  have hle := GammaOne.gam_le_div (s := KsIndex.AlphaRemark.spectralLower)
    trial_memDom hpos
  have hQ : Qform KsIndex.AlphaRemark.spectralLower trial < 0 := by
    refine lt_of_le_of_lt qform_le_grand ?_
    norm_num
  exact lt_of_le_of_lt hle (div_neg_of_neg_of_pos hQ hpos)

end KsIndex.NegSignProd
