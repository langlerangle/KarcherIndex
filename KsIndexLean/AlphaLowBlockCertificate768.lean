module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache768

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache768
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-15617 : ℤ)+i.val) : ℝ) *
        sample (2*((-15617 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-15617) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-15617) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 768 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+768 = -15617 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+768 = -15617 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-15617) (-2) center = -34196562737458261086094314828006363166728476394 ∧ blockLinearRadius (-15617) (-2) radius = 134528779127982716312426787851982418276 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-15617) (-1) center = 34194354681632345531521704973995255983359392136 ∧ blockLinearRadius (-15617) (-1) radius = 134520092626477462757905481657369474103 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-15617) (1) center = 34189939425328227051029060832217240501676179735 ∧ blockLinearRadius (-15617) (1) radius = 134502722988424987120108948926646561035 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-15617) (2) center = -34187732224739581699179246626643755393176971426 ∧ blockLinearRadius (-15617) (2) radius = 134494039851443279829605485013389476969 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache768
