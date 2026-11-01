module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11776

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache11776
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-4609 : ℤ)+i.val) : ℝ) *
        sample (2*((-4609 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-4609) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-4609) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 11776 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11776 = -4609 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11776 = -4609 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-4609) (-2) center = -171362386611266577023576856739908693629608280680 ∧ blockLinearRadius (-4609) (-2) radius = 902871364660280829878048538349021978425 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-4609) (-1) center = 171324112384286796894909908573818349266205178605 ∧ blockLinearRadius (-4609) (-1) radius = 902669691668322852373224990731904279190 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-4609) (1) center = 171247615213246983703512668066007345381847432222 ∧ blockLinearRadius (-4609) (1) radius = 902266615921503062526737486113472012702 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-4609) (2) center = -171209392246281501762967136165189541655344317558 ∧ blockLinearRadius (-4609) (2) radius = 902065213045931623299240488315462619459 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache11776
