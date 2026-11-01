module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17664

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache17664
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((1279 : ℤ)+i.val) : ℝ) *
        sample (2*((1279 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (1279) n center : ℝ)/10^51| ≤
      (blockLinearRadius (1279) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 17664 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17664 = 1279 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17664 = 1279 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (1279) (-2) center = 3186379696841117194896675951264041078528645311432 ∧ blockLinearRadius (1279) (-2) radius = 5381044894999335657638950461785427555963 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (1279) (-1) center = -3188658359852952506406655915621949063295001477556 ∧ blockLinearRadius (1279) (-1) radius = 5384893612302022649029128127823269467551 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (1279) (1) center = -3193225504198426772172123872459961228267641788445 ∧ blockLinearRadius (1279) (1) radius = 5392607632834475592217796161160583126687 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (1279) (2) center = 3195513999682857572729504322818230366301719258005 ∧ blockLinearRadius (1279) (2) radius = 5396472959972575120861037285368812426361 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache17664
