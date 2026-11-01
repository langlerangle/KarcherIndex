module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16896

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache16896
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((511 : ℤ)+i.val) : ℝ) *
        sample (2*((511 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (511) n center : ℝ)/10^51| ≤
      (blockLinearRadius (511) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 16896 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16896 = 511 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16896 = 511 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (511) (-2) center = 10488934404897950690333293655564247105918346703270 ∧ blockLinearRadius (511) (-2) radius = 18523389837006216790266266628512630444110 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (511) (-1) center = -10505888302140084147619732324540882535669822202589 ∧ blockLinearRadius (511) (-1) radius = 18553352567424494937128599851217374686698 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (511) (1) center = -10539963297612345693502215548873990905811298004979 ∧ blockLinearRadius (511) (1) radius = 18613573738643811443870673799708273276805 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (511) (2) center = 10557084953681458428635417723724301358397061745012 ∧ blockLinearRadius (511) (2) radius = 18643833166725263558292655891836913271463 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache16896
