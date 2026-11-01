module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache30464

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache30464
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((14079 : ℤ)+i.val) : ℝ) *
        sample (2*((14079 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (14079) n center : ℝ)/10^51| ≤
      (blockLinearRadius (14079) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 30464 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30464 = 14079 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30464 = 14079 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (14079) (-2) center = 103687338031012723455561543052582645217345295155 ∧ blockLinearRadius (14079) (-2) radius = 153534930034274820266810880454858353601 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (14079) (-1) center = -103694636333457812258672428093553727116041066128 ∧ blockLinearRadius (14079) (-1) radius = 153545737005701535453195105511036449322 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (14079) (1) center = -103709236021125158599325279069863020170296265806 ∧ blockLinearRadius (14079) (1) radius = 153567355513388622519101048996429573626 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (14079) (2) center = 103716537406781509839037548246983474233764164101 ∧ blockLinearRadius (14079) (2) radius = 153578167050291781248900891554911928868 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache30464
