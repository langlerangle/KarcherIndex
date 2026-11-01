module

public import KsIndexLean.AlphaEnergy8192PplusCertificate
public import KsIndexLean.AlphaEnergy8192PminusCertificate
public import KsIndexLean.AlphaEnergy8192MplusCertificate
public import KsIndexLean.AlphaEnergy8192MminusCertificate
public import KsIndexLean.AlphaEnergyWindow8192

@[expose] public section


/-! Lower bound for the four actual infinite energy tails. -/
namespace KsIndex.AlphaRemarkTrial.EnergyWindow8192

theorem tails_lower : (140376819/1000000000000 : ℝ) ≤ tails (12387581/10000000) := by
  have hp := Energy8192Tail.Pplus.corrected_tail_lower
  have hn := Energy8192Tail.Pminus.corrected_tail_lower
  have hm := Energy8192Tail.Mplus.corrected_tail_lower
  have hmn := Energy8192Tail.Mminus.corrected_tail_lower
  unfold tails
  linarith

end KsIndex.AlphaRemarkTrial.EnergyWindow8192
