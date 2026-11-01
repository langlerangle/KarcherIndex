module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache26368

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache26368
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((9983 : ℤ)+i.val) : ℝ) *
        sample (2*((9983 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (9983) n center : ℝ)/10^51| ≤
      (blockLinearRadius (9983) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 26368 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26368 = 9983 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26368 = 9983 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (9983) (-2) center = 171273887979478367521448516694320932223152162477 ∧ blockLinearRadius (9983) (-2) radius = 258618614726222575778536295336904221966 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (9983) (-1) center = -171290827906665622328454673819482758782648395706 ∧ blockLinearRadius (9983) (-1) radius = 258644193604469317174672225844631963963 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (9983) (1) center = -171324717816276743160559988089573214514391672077 ∧ blockLinearRadius (9983) (1) radius = 258695366544172173082340016092283560937 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (9983) (2) center = 171341667800690448325020889241413805156798707630 ∧ blockLinearRadius (9983) (2) radius = 258720960608632914737251871526892783667 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache26368
