module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18176

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache18176
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((1791 : ℤ)+i.val) : ℝ) *
        sample (2*((1791 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (1791) n center : ℝ)/10^51| ≤
      (blockLinearRadius (1791) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 18176 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18176 = 1791 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18176 = 1791 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (1791) (-2) center = 2006485093826487475026069225725472592043357860385 ∧ blockLinearRadius (1791) (-2) radius = 3329846268155159735079495143121268970609 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (1791) (-1) center = -2007533998499547712599854881533528101698624583831 ∧ blockLinearRadius (1791) (-1) radius = 3331587114177902168421901344625977557593 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (1791) (1) center = -2009635106121295154980294943854430884405765506447 ∧ blockLinearRadius (1791) (1) radius = 3335074280759420075964314334051454149591 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (1791) (2) center = 2010687312534062860402980123797233235798643890732 ∧ blockLinearRadius (1791) (2) radius = 3336820607068412632969811202321006858651 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache18176
