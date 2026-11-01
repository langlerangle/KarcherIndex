module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13312

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache13312
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-3073 : ℤ)+i.val) : ℝ) *
        sample (2*((-3073 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-3073) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-3073) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 13312 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13312 = -3073 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13312 = -3073 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-3073) (-2) center = -291539927452599597795463568939046282466841928346 ∧ blockLinearRadius (-3073) (-2) radius = 1722739559667274323157975658913095926073 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-3073) (-1) center = 291440758089816612857646001148594293836142165042 ∧ blockLinearRadius (-3073) (-1) radius = 1722153452521433379891715113246230408361 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-3073) (1) center = 291242621752987843423501396017446313083409668166 ∧ blockLinearRadius (-3073) (1) radius = 1720982434594510686126297391308426927693 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-3073) (2) center = -291143654641221396552916845070189448082309571716 ∧ blockLinearRadius (-3073) (2) radius = 1720397522999186020538048227351983116407 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache13312
