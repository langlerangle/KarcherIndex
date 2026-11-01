module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8448

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache8448
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-7937 : ℤ)+i.val) : ℝ) *
        sample (2*((-7937 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-7937) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-7937) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 8448 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8448 = -7937 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8448 = -7937 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-7937) (-2) center = -83827382073450262767019513273312084954889953837 ∧ blockLinearRadius (-7937) (-2) radius = 384591526107935828020952868757836685474 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-7937) (-1) center = 83816643774352795459137679356386605770911618578 ∧ blockLinearRadius (-7937) (-1) radius = 384542258834531299677611316180924015933 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-7937) (1) center = 83795175428248222926059061144491255044402335286 ∧ blockLinearRadius (-7937) (1) radius = 384443762149083685063920100500869955438 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-7937) (2) center = -83784445379127363672201463424348848839685816677 ∧ blockLinearRadius (-7937) (2) radius = 384394532727342292040185912067803758150 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache8448
