module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache13568

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache13568
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-2817 : ℤ)+i.val) : ℝ) *
        sample (2*((-2817 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-2817) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-2817) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 13568 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+13568 = -2817 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+13568 = -2817 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-2817) (-2) center = -326732376054082234288288084884700278320299956244 ∧ blockLinearRadius (-2817) (-2) radius = 1981943605629652379491516753825571860155 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-2817) (-1) center = 326610616849577727783294061632767984388373742141 ∧ blockLinearRadius (-2817) (-1) radius = 1981204857809366612974469317731580707673 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-2817) (1) center = 326367370690088675163294684546372208670152379777 ∧ blockLinearRadius (-2817) (1) radius = 1979729014346040604506369077798069077206 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-2817) (2) center = -326245883532113207449850569207991798411137080513 ∧ blockLinearRadius (-2817) (2) radius = 1978991917470857693238365828272246228107 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache13568
