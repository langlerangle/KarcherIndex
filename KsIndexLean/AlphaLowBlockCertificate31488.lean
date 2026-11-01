module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache31488

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache31488
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((15103 : ℤ)+i.val) : ℝ) *
        sample (2*((15103 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (15103) n center : ℝ)/10^51| ≤
      (blockLinearRadius (15103) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 31488 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+31488 = 15103 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+31488 = 15103 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (15103) (-2) center = 93572402904498628455572765362473748870616149075 ∧ blockLinearRadius (15103) (-2) radius = 138003407861497512154003076863064208010 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (15103) (-1) center = -93578546408562660663234045354102776919364168702 ∧ blockLinearRadius (15103) (-1) radius = 138012468499243820302033867615107221246 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (15103) (1) center = -93590835837179230257095835295624886686573023247 ∧ blockLinearRadius (15103) (1) radius = 138030593344555712899843455569196510121 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (15103) (2) center = 93596981762049679986196401099679175979996843829 ∧ blockLinearRadius (15103) (2) radius = 138039657552590165987183361323402305198 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache31488
