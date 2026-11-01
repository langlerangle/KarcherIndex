module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache26112

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache26112
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((9727 : ℤ)+i.val) : ℝ) *
        sample (2*((9727 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (9727) n center : ℝ)/10^51| ≤
      (blockLinearRadius (9727) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 26112 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26112 = 9727 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26112 = 9727 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (9727) (-2) center = 177883051643344013151341405343044367622421535569 ∧ blockLinearRadius (9727) (-2) radius = 268993726420388946322917607134588796878 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (9727) (-1) center = -177901102355707138755837316552080400236627458895 ∧ blockLinearRadius (9727) (-1) radius = 269021022691710720993427154221920203196 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (9727) (1) center = -177937214773476892879934770696532456989110781306 ∧ blockLinearRadius (9727) (1) radius = 269075631858078577250545544018619944361 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (9727) (2) center = 177955276481115493722395299684884851525977564872 ∧ blockLinearRadius (9727) (2) radius = 269102944756499867186141543168206850358 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache26112
