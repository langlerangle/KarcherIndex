module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23552

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache23552
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((7167 : ℤ)+i.val) : ℝ) *
        sample (2*((7167 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (7167) n center : ℝ)/10^51| ≤
      (blockLinearRadius (7167) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 23552 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23552 = 7167 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23552 = 7167 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (7167) (-2) center = 277390049268409798331876625433876593105094240616 ∧ blockLinearRadius (7167) (-2) radius = 426757089749317147992918821998392501148 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (7167) (-1) center = -277428078404748021882359425627901110650444997796 ∧ blockLinearRadius (7167) (-1) radius = 426815596890430299011259583622680277202 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (7167) (1) center = -277504167971128979578535309242384328709220314734 ∧ blockLinearRadius (7167) (1) radius = 426932659317739655008920059619651766245 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (7167) (2) center = 277542228409757506236686697208345520266281605987 ∧ blockLinearRadius (7167) (2) radius = 426991214617145102064348523814246702826 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache23552
