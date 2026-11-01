module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13824

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache13824
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-2561 : ℤ)+i.val) : ℝ) *
        sample (2*((-2561 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-2561) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-2561) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 13824 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13824 = -2561 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13824 = -2561 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-2561) (-2) center = -370182221244159574987319154961360026467396646838 ∧ blockLinearRadius (-2561) (-2) radius = 2312587693720398638366428276731379433134 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-2561) (-1) center = 370029692236838318598633787384672416589686530615 ∧ blockLinearRadius (-2561) (-1) radius = 2311634559444588608204831344904732253036 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-2561) (1) center = 369725011345641189852052678889429675286688587914 ∧ blockLinearRadius (-2561) (1) radius = 2309730648133476799313194601864985109830 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-2561) (2) center = -369572859150798510202628110697686089762685897105 ∧ blockLinearRadius (-2561) (2) radius = 2308779869153922082935711490460639224022 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache13824
