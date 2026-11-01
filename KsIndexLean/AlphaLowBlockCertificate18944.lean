module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18944

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache18944
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((2559 : ℤ)+i.val) : ℝ) *
        sample (2*((2559 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (2559) n center : ℝ)/10^51| ≤
      (blockLinearRadius (2559) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 18944 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18944 = 2559 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18944 = 2559 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (2559) (-2) center = 1216886659500135382054453201652377642177845002331 ∧ blockLinearRadius (2559) (-2) radius = 1981507384898462982163613731558894720412 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (2559) (-1) center = -1217340221296405691322102119778010347941032303727 ∧ blockLinearRadius (2559) (-1) radius = 1982245970000564775719710259134821131571 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (2559) (1) center = -1218248360732461555470179930136337631444684899913 ∧ blockLinearRadius (2559) (1) radius = 1983724794486177402700889418615755903914 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (2559) (2) center = 1218702939131500253280511195302458287075464607157 ∧ blockLinearRadius (2559) (2) radius = 1984465035106169783205829569030899042976 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache18944
