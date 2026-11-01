module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23040

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache23040
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((6655 : ℤ)+i.val) : ℝ) *
        sample (2*((6655 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (6655) n center : ℝ)/10^51| ≤
      (blockLinearRadius (6655) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 23040 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23040 = 6655 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23040 = 6655 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (6655) (-2) center = 308886429925562180917808238023182431167783759847 ∧ blockLinearRadius (6655) (-2) radius = 477194364463131017763510158662124880961 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (6655) (-1) center = -308931974926239212837613419223991695137537397826 ∧ blockLinearRadius (6655) (-1) radius = 477264726780450478901082389027845868652 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (6655) (1) center = -309023105237659136400960964320914302953924564212 ∧ blockLinearRadius (6655) (1) radius = 477405513690395877648370592638750205862 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (6655) (2) center = 309068690560297472826404608697690335541538218922 ∧ blockLinearRadius (6655) (2) radius = 477475938301399296794120302359468323069 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache23040
