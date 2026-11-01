module

public import KsIndexLean.AlphaEnergy8192TableInterface
public import KsIndexLean.ProdWindowGlue

@[expose] public section


/-! Concrete lower bound for `Qform (12387581/10000000) trial`, combining
the certified finite window with the four reciprocal-corrected energy tails. -/
namespace KsIndex.AlphaRemarkTrial.EnergyWindow8192

 theorem qform_lower : (1628/1000000000 : ℝ) ≤
    CircleQ.Qform (12387581/10000000) trial := by
  have h := qform_ge_table_and_tails NegSignProd.valid
    (by simpa only [add_zero, NegSignProd.window] using NegSignProd.window_covered_P)
    (by simpa only [NegSignProd.window] using NegSignProd.window_covered_M)
  change _ ≤ CircleQ.Qform _ trial at h
  change (((tableEnergyNumerator NegSignProd.t NegSignProd.window 1 0 : ℝ) -
    tableEnergyRadius NegSignProd.t NegSignProd.window 1 0 +
    (12387581/10000000 : ℝ)^2 *
      ((tableEnergyNumerator NegSignProd.t NegSignProd.window 4 1 : ℝ) -
       tableEnergyRadius NegSignProd.t NegSignProd.window 4 1)) / (10^51 : ℝ)^2) +
     140376819/1000000000000 ≤ _ at h
  rw [NegSignProd.window_P_c, NegSignProd.window_P_r,
    NegSignProd.window_Mm_c, NegSignProd.window_Mm_r] at h
  norm_num at h ⊢
  linarith

end KsIndex.AlphaRemarkTrial.EnergyWindow8192
