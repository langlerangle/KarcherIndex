module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache32512

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache32512
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((16127 : ℤ)+i.val) : ℝ) *
        sample (2*((16127 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (16127) n center : ℝ)/10^51| ≤
      (blockLinearRadius (16127) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 32512 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32512 = 16127 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32512 = 16127 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (16127) (-2) center = 85011773311993939457093255176269037932671719729 ∧ blockLinearRadius (16127) (-2) radius = 124909127625010542223776060819524915213 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (16127) (-1) center = -85017003142264311262819649449320041396747101308 ∧ blockLinearRadius (16127) (-1) radius = 124916811905536272741369536979108545030 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (16127) (1) center = -85027464733482750285314115196687301760086130373 ∧ blockLinearRadius (16127) (1) radius = 124932183303369408634306740145109934204 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (16127) (2) center = 85032696494668417487554314418928879885489906172 ∧ blockLinearRadius (16127) (2) radius = 124939870421025924629479478700115143052 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache32512
