module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache5376

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache5376
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-11009 : ℤ)+i.val) : ℝ) *
        sample (2*((-11009 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-11009) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-11009) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 5376 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5376 = -11009 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5376 = -11009 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-11009) (-2) center = -54395323183648026236707469979782722699495323900 ∧ blockLinearRadius (-11009) (-2) radius = 231165691764149943887112895531288257376 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-11009) (-1) center = 54390323080877927910072363183774175125767700437 ∧ blockLinearRadius (-11009) (-1) radius = 231144442433760834114244200910598332007 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-11009) (1) center = 54380325632661379167528255685408963184008662274 ∧ blockLinearRadius (-11009) (1) radius = 231101955491119402506471244730750607974 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-11009) (2) center = -54375328286708106801080577125172649032817054426 ∧ blockLinearRadius (-11009) (2) radius = 231080717876713154901960838756405665780 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache5376
