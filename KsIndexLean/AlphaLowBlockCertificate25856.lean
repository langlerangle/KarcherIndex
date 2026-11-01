module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache25856

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache25856
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((9471 : ℤ)+i.val) : ℝ) *
        sample (2*((9471 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (9471) n center : ℝ)/10^51| ≤
      (blockLinearRadius (9471) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 25856 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+25856 = 9471 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+25856 = 9471 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (9471) (-2) center = 184931994954520017390271781632396464189040695266 ∧ blockLinearRadius (9471) (-2) radius = 280075583840476999086221875992302524823 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (9471) (-1) center = -184951261531495768926066041849816054204114452532 ∧ blockLinearRadius (9471) (-1) radius = 280104762761807361821753752364864921206 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (9471) (1) center = -184989806732049421242097537838855534115328739156 ∧ blockLinearRadius (9471) (1) radius = 280163138848915529798817706096538768581 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (9471) (2) center = 185009085358138481690724929832866372163016427233 ∧ blockLinearRadius (9471) (2) radius = 280192336018496471868062337607199416181 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache25856
