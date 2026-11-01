module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache29696

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache29696
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((13311 : ℤ)+i.val) : ℝ) *
        sample (2*((13311 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (13311) n center : ℝ)/10^51| ≤
      (blockLinearRadius (13311) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 29696 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29696 = 13311 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29696 = 13311 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (13311) (-2) center = 112545246372589816540549842294074874578918764211 ∧ blockLinearRadius (13311) (-2) radius = 167184867441136711673602257657457645376 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (13311) (-1) center = -112553620901558124104870482462485492714299243419 ∧ blockLinearRadius (13311) (-1) radius = 167197307743992956776888998598822780400 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (13311) (1) center = -112570373699073149990608536217502836966567720069 ∧ blockLinearRadius (13311) (1) radius = 167222193904832076651965144982137686276 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (13311) (2) center = 112578751968176552777583617401197786287903235850 ∧ blockLinearRadius (13311) (2) radius = 167234639763641905089857925276921245333 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache29696
