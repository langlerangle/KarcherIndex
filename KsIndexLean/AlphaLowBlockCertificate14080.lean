module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14080

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache14080
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-2305 : ℤ)+i.val) : ℝ) *
        sample (2*((-2305 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-2305) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-2305) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 14080 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14080 = -2305 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14080 = -2305 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-2305) (-2) center = -424994739446261224033899792554051668413948291140 ∧ blockLinearRadius (-2305) (-2) radius = 2745484295201305394003392695957214615860 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-2305) (-1) center = 424798924285370516956815715992888481149331239540 ∧ blockLinearRadius (-2305) (-1) radius = 2744218876787544228539477930445251835905 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-2305) (1) center = 424407835416693988666979496051484036056273043801 ∧ blockLinearRadius (-2305) (1) radius = 2741691540223159582401195920541508740771 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-2305) (2) center = -424212561209503141530384520986388996342945898012 ∧ blockLinearRadius (-2305) (2) radius = 2740429618842969762408988591479653243095 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache14080
