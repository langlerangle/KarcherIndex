module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache1536

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache1536
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-14849 : ℤ)+i.val) : ℝ) *
        sample (2*((-14849 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-14849) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-14849) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 1536 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1536 = -14849 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1536 = -14849 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-14849) (-2) center = -36568837685671984246974240439468906317998928213 ∧ blockLinearRadius (-14849) (-2) radius = 145432827540593161953312239300807980016 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-14849) (-1) center = 36566353244481930552877974980896976808475866194 ∧ blockLinearRadius (-14849) (-1) radius = 145422946962407992338284741890096758265 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-14849) (1) center = 36561385374728750782935537830510842522668378706 ∧ blockLinearRadius (-14849) (1) radius = 145403189833258597400324442459230489766 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-14849) (2) center = -36558901946028052593906928787191408675518869375 ∧ blockLinearRadius (-14849) (2) radius = 145393313281747244330937410594538883680 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache1536
