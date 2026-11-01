module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20224

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache20224
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((3839 : ℤ)+i.val) : ℝ) *
        sample (2*((3839 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (3839) n center : ℝ)/10^51| ≤
      (blockLinearRadius (3839) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 20224 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20224 = 3839 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20224 = 3839 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (3839) (-2) center = 683049854985910615486689095871154359435677888518 ∧ blockLinearRadius (3839) (-2) radius = 1087971739944690092129743669285620339123 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (3839) (-1) center = -683222142789707190396316433937231005091241600939 ∧ blockLinearRadius (3839) (-1) radius = 1088246167863080946048335155879538506349 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (3839) (1) center = -683566979359665191802649798770312394249179727528 ∧ blockLinearRadius (3839) (1) radius = 1088795439380868088757035385353446515571 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (3839) (2) center = 683739528257664553205256721635626599945451357028 ∧ blockLinearRadius (3839) (2) radius = 1089070283190270148615429544251076504022 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache20224
