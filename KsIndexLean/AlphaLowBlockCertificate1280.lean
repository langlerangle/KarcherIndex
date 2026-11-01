module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache1280

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache1280
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-15105 : ℤ)+i.val) : ℝ) *
        sample (2*((-15105 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-15105) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-15105) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 1280 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1280 = -15105 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1280 = -15105 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-15105) (-2) center = -35747000864098797004017874337281276580480987645 ∧ blockLinearRadius (-15105) (-2) radius = 141640426634825729470117803339387580068 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-15105) (-1) center = 35744613776818825282480350765702985645568395600 ∧ blockLinearRadius (-15105) (-1) radius = 141630968223954481954027710849892351642 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-15105) (1) center = 35739840558573536674123660271685301269468539988 ∧ blockLinearRadius (-15105) (1) radius = 141612055191459285100973808033435999267 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-15105) (2) center = -35737454427480518980084861848141998058389078691 ∧ blockLinearRadius (-15105) (2) radius = 141602600569329338647305524837137957629 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache1280
