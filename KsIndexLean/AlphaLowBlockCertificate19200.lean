module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19200

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache19200
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((2815 : ℤ)+i.val) : ℝ) *
        sample (2*((2815 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (2815) n center : ℝ)/10^51| ≤
      (blockLinearRadius (2815) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 19200 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19200 = 2815 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19200 = 2815 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (2815) (-2) center = 1063213313342296411009630883720239566928878794370 ∧ blockLinearRadius (2815) (-2) radius = 1722393131854378458745209874491283623174 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (2815) (-1) center = -1063575024817986268283675277876330151117015925083 ∧ blockLinearRadius (2815) (-1) radius = 1722979121065701541967340919426183277300 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (2815) (1) center = -1064299187076923928301483220700285733194395156891 ∧ blockLinearRadius (2815) (1) radius = 1724152297243163085665262965992762370521 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (2815) (2) center = 1064661638364355222714886060866111737838249615600 ∧ blockLinearRadius (2815) (2) radius = 1724739485026160029505404669758643360067 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache19200
