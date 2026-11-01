module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24320

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache24320
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((7935 : ℤ)+i.val) : ℝ) *
        sample (2*((7935 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (7935) n center : ℝ)/10^51| ≤
      (blockLinearRadius (7935) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 24320 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24320 = 7935 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24320 = 7935 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (7935) (-2) center = 239254417295956693544463706740687865248742760701 ∧ blockLinearRadius (7935) (-2) radius = 365984292752324684027921105824121370576 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (7935) (-1) center = -239284092916519926256156302425777923006555851028 ∧ blockLinearRadius (7935) (-1) radius = 366029687371742688444126384151489608323 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (7935) (1) center = -239343466249652036306102354346527840734933299038 ∧ blockLinearRadius (7935) (1) radius = 366120510404750178536681394011390704835 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (7935) (2) center = 239373163967704183377681348072976289234561109771 ∧ blockLinearRadius (7935) (2) radius = 366165938826727469803905400652995370792 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache24320
