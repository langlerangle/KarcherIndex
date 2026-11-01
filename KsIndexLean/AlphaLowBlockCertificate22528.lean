module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22528

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache22528
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((6143 : ℤ)+i.val) : ℝ) *
        sample (2*((6143 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (6143) n center : ℝ)/10^51| ≤
      (blockLinearRadius (6143) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 22528 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22528 = 6143 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22528 = 6143 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (6143) (-2) center = 346885653970675390659453757294773950760922652401 ∧ blockLinearRadius (6143) (-2) radius = 538306485011110400321777393837537210690 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (6143) (-1) center = -346940980030258690632448135242235620388952997169 ∧ blockLinearRadius (6143) (-1) radius = 538392342158333087033209706758681031414 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (6143) (1) center = -347051685118609456667242976444105273936135406652 ∧ blockLinearRadius (6143) (1) radius = 538564138653085458401214374922049895470 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (6143) (2) center = 347107064164286206518461864883370054314806281182 ∧ blockLinearRadius (6143) (2) radius = 538650078026856048075854504782849380956 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache22528
