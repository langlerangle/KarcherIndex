module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache17152

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache17152
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((767 : ℤ)+i.val) : ℝ) *
        sample (2*((767 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (767) n center : ℝ)/10^51| ≤
      (blockLinearRadius (767) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 17152 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+17152 = 767 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+17152 = 767 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (767) (-2) center = 6282039806873447612337120143071606027757464008180 ∧ blockLinearRadius (767) (-2) radius = 10882783039683385685548485201335213318051 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (767) (-1) center = -6289171917959202622821008977060171538383309328519 ∧ blockLinearRadius (767) (-1) radius = 10895143132861427963826902436390151540762 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (767) (1) center = -6303485169190136312068630714829670115093054709239 ∧ blockLinearRadius (767) (1) radius = 10919948319406863624831502428016784334719 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (767) (2) center = 6310666422576352616285020898161430495554767843290 ∧ blockLinearRadius (767) (2) radius = 10932393609168940333048215890488066467495 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache17152
