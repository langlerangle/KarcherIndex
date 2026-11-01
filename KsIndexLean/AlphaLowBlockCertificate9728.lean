module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9728

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache9728
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-6657 : ℤ)+i.val) : ℝ) *
        sample (2*((-6657 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-6657) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-6657) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 9728 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9728 = -6657 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9728 = -6657 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-6657) (-2) center = -105693591080016979295481497573530589540577126833 ∧ blockLinearRadius (-6657) (-2) radius = 506276179065258535008616916517843837218 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-6657) (-1) center = 105677395517661576673443014477395012254736102834 ∧ blockLinearRadius (-6657) (-1) radius = 506198599296842748080419487121610057899 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-6657) (1) center = 105645019280294498226288108690179719515227845819 ∧ blockLinearRadius (-6657) (1) radius = 506043511075401156777115155318608031066 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-6657) (2) center = -105628838600721337832435811747890360005761253489 ∧ blockLinearRadius (-6657) (2) radius = 505966002600523621272203246370293274140 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache9728
