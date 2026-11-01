module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache7424

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache7424
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-8961 : ℤ)+i.val) : ℝ) *
        sample (2*((-8961 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-8961) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-8961) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 7424 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+7424 = -8961 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+7424 = -8961 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-8961) (-2) center = -71418546362408270468403332158443950251413006659 ∧ blockLinearRadius (-8961) (-2) radius = 318319179817479935152153841367166625228 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-8961) (-1) center = 71410458719898693577169210089301150108464921132 ∧ blockLinearRadius (-8961) (-1) radius = 318283131847729307660093299420222272068 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-8961) (1) center = 71394288929227754500556195642644435347989343287 ∧ blockLinearRadius (-8961) (1) radius = 318211060397851324744459259235279932738 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-8961) (2) center = -71386206779822249111200073698140276293807231117 ∧ blockLinearRadius (-8961) (2) radius = 318175036912178435553789311376139973084 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache7424
