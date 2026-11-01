module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache28928

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache28928
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((12543 : ℤ)+i.val) : ℝ) *
        sample (2*((12543 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (12543) n center : ℝ)/10^51| ≤
      (blockLinearRadius (12543) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 28928 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28928 = 12543 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28928 = 12543 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (12543) (-2) center = 122752405599664047202113460069529517441961894748 ∧ blockLinearRadius (12543) (-2) radius = 182965523154064534543845585588041385829 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (12543) (-1) center = -122762093315955859705225915122160883167941440177 ∧ blockLinearRadius (12543) (-1) radius = 182979962965131429991479093397370181640 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (12543) (1) center = -122781473336792857823547447867814643762433629189 ∧ blockLinearRadius (12543) (1) radius = 183008849426198090171179768297681241731 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (12543) (2) center = 122791165642062481363199937611500367854765650878 ∧ blockLinearRadius (12543) (2) radius = 183023296077277654037499522574699035258 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache28928
