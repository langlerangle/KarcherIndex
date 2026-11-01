module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache25088

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache25088
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((8703 : ℤ)+i.val) : ℝ) *
        sample (2*((8703 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (8703) n center : ℝ)/10^51| ≤
      (blockLinearRadius (8703) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 25088 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25088 = 8703 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25088 = 8703 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (8703) (-2) center = 209167431696156581338025202496909437975905559422 ∧ blockLinearRadius (8703) (-2) radius = 318297611573896244463669543227090454371 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (8703) (-1) center = -209191118710467249353900560304583822846808765030 ∧ blockLinearRadius (8703) (-1) radius = 318333657100987876410930232562617150299 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (8703) (1) center = -209238508838374979307275814633658368136352874261 ∧ blockLinearRadius (8703) (1) radius = 318405772654231445916362027381213213679 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (8703) (2) center = 209262211955620095568278981166389241477689982480 ∧ blockLinearRadius (8703) (2) radius = 318441842685934825893490956507033463909 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache25088
