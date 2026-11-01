module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18688

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache18688
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((2303 : ℤ)+i.val) : ℝ) *
        sample (2*((2303 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (2303) n center : ℝ)/10^51| ≤
      (blockLinearRadius (2303) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 18688 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18688 = 2303 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18688 = 2303 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (2303) (-2) center = 1411862294038105357317823556031800145089387746317 ∧ blockLinearRadius (2303) (-2) radius = 2312025484581141021499456952104421253031 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (2303) (-1) center = -1412444163469643406701692725576926393816975061705 ∧ blockLinearRadius (2303) (-1) radius = 2312978386930279895881906052799171221415 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (2303) (1) center = -1413609343684524021811391575629816192386651277319 ∧ blockLinearRadius (2303) (1) radius = 2314886552190552522659864942749430488294 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (2303) (2) center = 1414192655659585586197381861898985925199964840396 ∧ blockLinearRadius (2303) (2) radius = 2315841817053515350081610898287908160363 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache18688
