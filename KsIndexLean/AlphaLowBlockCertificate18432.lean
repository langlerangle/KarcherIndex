module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache18432

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache18432
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((2047 : ℤ)+i.val) : ℝ) *
        sample (2*((2047 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (2047) n center : ℝ)/10^51| ≤
      (blockLinearRadius (2047) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 18432 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+18432 = 2047 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+18432 = 2047 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (2047) (-2) center = 1665619547551720626743788873034123259346402686299 ∧ blockLinearRadius (2047) (-2) radius = 2744738770424925903123882575765429764522 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (2047) (-1) center = -1666387196581979558559777746436141123520475723737 ∧ blockLinearRadius (2047) (-1) radius = 2746003844827032466781926884121439601278 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (2047) (1) center = -1667924621818979118349823852496974323815930579156 ∧ blockLinearRadius (2047) (1) radius = 2748537499414051747176921976308942291612 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (2047) (2) center = 1668694399993719145200206865176646937688893613216 ∧ blockLinearRadius (2047) (2) radius = 2749806082842618165630462408596680196097 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache18432
