module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20480

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache20480
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((4095 : ℤ)+i.val) : ℝ) *
        sample (2*((4095 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (4095) n center : ℝ)/10^51| ≤
      (blockLinearRadius (4095) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 20480 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20480 = 4095 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20480 = 4095 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (4095) (-2) center = 622639691412002695578747173491742035101388155321 ∧ blockLinearRadius (4095) (-2) radius = 988233832440479100545856417509027087587 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (4095) (-1) center = -622787208624428239230979042127335447677123854014 ∧ blockLinearRadius (4095) (-1) radius = 988467971117715010795026138776978151735 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (4095) (1) center = -623082452913673001758506281154108408012781203340 ∧ blockLinearRadius (4095) (1) radius = 988936581573827111975932299402112532754 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (4095) (2) center = 623230180090067057728597524195836400980557293600 ∧ blockLinearRadius (4095) (2) radius = 989171053510753541842909020543950468256 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache20480
