module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache1792

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache1792
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-14593 : ℤ)+i.val) : ℝ) *
        sample (2*((-14593 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-14593) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-14593) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 1792 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1792 = -14593 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1792 = -14593 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-14593) (-2) center = -37424166359605414032722351671401614424481530530 ∧ blockLinearRadius (-14593) (-2) radius = 149396180853809811742460709211412484594 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-14593) (-1) center = 37421578802182269916491750513400097334340718609 ∧ blockLinearRadius (-14593) (-1) radius = 149385851342055489840671993841486821945 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-14593) (1) center = 37416404760658871191533572584711881827673485412 ∧ blockLinearRadius (-14593) (1) radius = 149365196603268613293413758150370769166 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-14593) (2) center = -37413818276410217628814075732967227776307332515 ∧ blockLinearRadius (-14593) (2) radius = 149354871375643644378176425095080820562 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache1792
