module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache32256

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache32256
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((15871 : ℤ)+i.val) : ℝ) *
        sample (2*((15871 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (15871) n center : ℝ)/10^51| ≤
      (blockLinearRadius (15871) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 32256 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32256 = 15871 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32256 = 15871 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (15871) (-2) center = 87025026699146679418271873439156309937717329753 ∧ blockLinearRadius (15871) (-2) radius = 127984165682072562149793252104002917738 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (15871) (-1) center = -87030466050452980456074368429691877525753379288 ∧ blockLinearRadius (15871) (-1) radius = 127992165124535315985101257308850228505 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (15871) (1) center = -87041346793228566860571814354495104178274432908 ∧ blockLinearRadius (15871) (1) radius = 128008167009852880947756364809162028007 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (15871) (2) center = 87046788184952944780768194705933974583958116108 ∧ blockLinearRadius (15871) (2) radius = 128016169453082847696249367133820528481 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache32256
