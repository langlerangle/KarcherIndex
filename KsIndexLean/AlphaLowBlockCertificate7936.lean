module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache7936

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache7936
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-8449 : ℤ)+i.val) : ℝ) *
        sample (2*((-8449 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-8449) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-8449) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 7936 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7936 = -8449 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7936 = -8449 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-8449) (-2) center = -77189146684280546057712147058420684196947869593 ∧ blockLinearRadius (-8449) (-2) radius = 348869884417603235272849275052026196701 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-8449) (-1) center = 77179867458889458558944953204548003991960938567 ∧ blockLinearRadius (-8449) (-1) radius = 348827944555029350598580476272317945562 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-8449) (1) center = 77161315699989729026872034910589258318611019389 ∧ blockLinearRadius (-8449) (1) radius = 348744095076137139538035613327729768751 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-8449) (2) center = -77152043164872495875751088485367921869782951484 ∧ blockLinearRadius (-8449) (2) radius = 348702185452548099974688835640669047045 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache7936
