module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache2816

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache2816
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-13569 : ℤ)+i.val) : ℝ) *
        sample (2*((-13569 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-13569) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-13569) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 2816 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2816 = -13569 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2816 = -13569 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-13569) (-2) center = -41222518177183067309337181320043466060158588101 ∧ blockLinearRadius (-13569) (-2) radius = 167192347268802470571542521779253948778 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-13569) (-1) center = 41219450810808206715108746046094190775137598978 ∧ blockLinearRadius (-13569) (-1) radius = 167179906409352177546189435399732406947 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-13569) (1) center = 41213317447351955411462329123434801176774487261 ∧ blockLinearRadius (-13569) (1) radius = 167155030244173405607171763012590646208 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-13569) (2) center = -41210251450066819692496185333471752999157769744 ∧ blockLinearRadius (-13569) (2) radius = 167142594937618551220741393191991212125 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache2816
