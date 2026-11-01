module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache29184

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache29184
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((12799 : ℤ)+i.val) : ℝ) *
        sample (2*((12799 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (12799) n center : ℝ)/10^51| ≤
      (blockLinearRadius (12799) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 29184 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29184 = 12799 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29184 = 12799 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (12799) (-2) center = 119182807041224741576499326896077332836580911109 ∧ blockLinearRadius (12799) (-2) radius = 177440784844264821110615133723737470706 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (12799) (-1) center = -119192026754090191996978195543259758676000935903 ∧ blockLinearRadius (12799) (-1) radius = 177454511288547635767919110589799704068 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (12799) (1) center = -119210470459920196925192294996266230104158394826 ∧ blockLinearRadius (12799) (1) radius = 177481970549399812260507727460381882823 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (12799) (2) center = 119219694453547146058404072355242944009320094244 ∧ blockLinearRadius (12799) (2) radius = 177495703366955360674338737181044705964 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache29184
