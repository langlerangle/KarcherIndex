module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12800

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache12800
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-3585 : ℤ)+i.val) : ℝ) *
        sample (2*((-3585 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-3585) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-3585) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 12800 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12800 = -3585 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12800 = -3585 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-3585) (-2) center = -238233980926870862635605595482912039530900487171 ∧ blockLinearRadius (-3585) (-2) radius = 1345860747528822508242090154906453882387 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-3585) (-1) center = 238164976094228821545316672374176036197207448829 ∧ blockLinearRadius (-3585) (-1) radius = 1345470867832273631401258580013690715441 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-3585) (1) center = 238027086338411572262660014719568117097879056553 ∧ blockLinearRadius (-3585) (1) radius = 1344691786017034748785075501999209589838 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-3585) (2) center = -237958201345769363695063434264092121359775715482 ∧ blockLinearRadius (-3585) (2) radius = 1344302583505755119517867117512722350938 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache12800
