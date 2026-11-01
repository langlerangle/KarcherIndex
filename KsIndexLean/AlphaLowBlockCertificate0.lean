module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache0

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache0
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-16385 : ℤ)+i.val) : ℝ) *
        sample (2*((-16385 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-16385) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-16385) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 0 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+0 = -16385 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+0 = -16385 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-16385) (-2) center = -32080023927549133727023149812153451125143000332 ∧ blockLinearRadius (-16385) (-2) radius = 124913758152107028912128493442915715041 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-16385) (-1) center = 32078050406225435657970135810743102480396824924 ∧ blockLinearRadius (-16385) (-1) radius = 124906073586710235781845530779012845221 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-16385) (1) center = 32074104091954254357420263121267846700553034080 ∧ blockLinearRadius (-16385) (1) radius = 124890707292105459120309115601614871575 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-16385) (2) center = -32072131298917166446383338429599461340877377738 ∧ blockLinearRadius (-16385) (2) radius = 124883025562548566750964415423359892368 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache0
