module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache4096

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache4096
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-12289 : ℤ)+i.val) : ℝ) *
        sample (2*((-12289 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-12289) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-12289) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 4096 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4096 = -12289 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4096 = -12289 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-12289) (-2) center = -47016101802557665446626674183581378651514629499 ∧ blockLinearRadius (-12289) (-2) radius = 194917584184188253331991964876543278070 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-12289) (-1) center = 47012235016573406063107503885277538595762659803 ∧ blockLinearRadius (-12289) (-1) radius = 194901553277777836627628551664307639522 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-12289) (1) center = 47004503352478093921550680223642346895602269474 ∧ blockLinearRadius (-12289) (1) radius = 194869499374674855327619661472271744181 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-12289) (2) center = -47000638474053273671055183594696291259492158729 ∧ blockLinearRadius (-12289) (2) radius = 194853476376681453467490223201707375366 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache4096
