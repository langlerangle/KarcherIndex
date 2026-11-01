module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24064

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache24064
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((7679 : ℤ)+i.val) : ℝ) *
        sample (2*((7679 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (7679) n center : ℝ)/10^51| ≤
      (blockLinearRadius (7679) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 24064 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24064 = 7679 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24064 = 7679 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (7679) (-2) center = 250935391258286964249019502012149183866381275024 ∧ blockLinearRadius (7679) (-2) radius = 384562089837352765493841972052320667629 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (7679) (-1) center = -250967536633916724779221632582126786545082973291 ∧ blockLinearRadius (7679) (-1) radius = 384611353339552930877632097489235888859 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (7679) (1) center = -251031852101083204405337360202737008363776844594 ∧ blockLinearRadius (7679) (1) radius = 384709918221823875683909419809430385506 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (7679) (2) center = 251064022198955817874377938969521875108768342295 ∧ blockLinearRadius (7679) (2) radius = 384759219611604653523685692338926687586 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache24064
