module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache3840

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache3840
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-12545 : ℤ)+i.val) : ℝ) *
        sample (2*((-12545 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-12545) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-12545) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 3840 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3840 = -12545 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3840 = -12545 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-12545) (-2) center = -45747619179422446718874938341439505533839875830 ∧ blockLinearRadius (-12545) (-2) radius = 188789799656268563645175033040332511463 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-12545) (-1) center = 45743934307632360252321566740881488707264243480 ∧ blockLinearRadius (-12545) (-1) radius = 188774592927645397705895000958258302474 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-12545) (1) center = 45736566344679130324345626689651851368321414131 ∧ blockLinearRadius (-12545) (1) radius = 188744186818747469263733861890860741136 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-12545) (2) center = -45732883253229184552125584968658866657492748444 ∧ blockLinearRadius (-12545) (2) radius = 188728987437289112559175939675952217349 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache3840
