module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19968

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache19968
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((3583 : ℤ)+i.val) : ℝ) *
        sample (2*((3583 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (3583) n center : ℝ)/10^51| ≤
      (blockLinearRadius (3583) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 19968 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19968 = 3583 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19968 = 3583 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (3583) (-2) center = 753986065056188883438372667322074745211831151055 ∧ blockLinearRadius (3583) (-2) radius = 1205514313081652344624434209043394988862 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (3583) (-1) center = -754189386208710199087917534901014335038924297864 ∧ blockLinearRadius (3583) (-1) radius = 1205839401404115661006433355833564253746 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (3583) (1) center = -754596357789468508760605179677637440521719920398 ∧ blockLinearRadius (3583) (1) radius = 1206490104536781853976591802307261338265 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (3583) (2) center = 754800008395576489116896092993846529271329704972 ∧ blockLinearRadius (3583) (2) radius = 1206815719631393784186024375336731476265 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache19968
