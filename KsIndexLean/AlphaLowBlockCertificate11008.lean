module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11008

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache11008
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-5377 : ℤ)+i.val) : ℝ) *
        sample (2*((-5377 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-5377) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-5377) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 11008 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11008 = -5377 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11008 = -5377 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-5377) (-2) center = -139966918986264221555834986313655207609858305884 ∧ blockLinearRadius (-5377) (-2) radius = 707946319732024990986181197509332942775 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-5377) (-1) center = 139940236386297086699146062242873570225622676756 ∧ blockLinearRadius (-5377) (-1) radius = 707811353550633948151221967521461386804 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-5377) (1) center = 139886901700609487905628747771575758491222870475 ∧ blockLinearRadius (-5377) (1) radius = 707541575543079430193612331019648305803 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-5377) (2) center = -139860249603256896998690501081903000358640346628 ∧ blockLinearRadius (-5377) (2) radius = 707406763658072294483692589792753837328 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache11008
