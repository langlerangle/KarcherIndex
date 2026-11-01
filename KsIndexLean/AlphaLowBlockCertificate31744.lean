module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache31744

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache31744
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((15359 : ℤ)+i.val) : ℝ) *
        sample (2*((15359 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (15359) n center : ℝ)/10^51| ≤
      (blockLinearRadius (15359) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 31744 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+31744 = 15359 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+31744 = 15359 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (15359) (-2) center = 91300463863586815928628382227776443354780796752 ∧ blockLinearRadius (15359) (-2) radius = 134523547843140127762646494211532096229 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (15359) (-1) center = -91306359112036965449062417854381608062934180246 ∧ blockLinearRadius (15359) (-1) radius = 134532234006854565391352641009929313872 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (15359) (1) center = -91318151893212704144166910361064492467548632702 ∧ blockLinearRadius (15359) (1) radius = 134549609699979833718260864148919941920 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (15359) (2) center = 91324049426233354116022037466002386347048273599 ∧ blockLinearRadius (15359) (2) radius = 134558299229825413372413923081543807038 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache31744
