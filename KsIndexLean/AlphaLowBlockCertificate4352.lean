module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache4352

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache4352
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-12033 : ℤ)+i.val) : ℝ) *
        sample (2*((-12033 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-12033) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-12033) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 4352 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4352 = -12033 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4352 = -12033 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-12033) (-2) center = -48347226876467331374543277363101649352089122428 ∧ blockLinearRadius (-12033) (-2) radius = 201381436451176361596930403611515929145 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-12033) (-1) center = 48343165087601518839980899135898291797753852519 ∧ blockLinearRadius (-12033) (-1) radius = 201364517676072653613075505229837158942 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-12033) (1) center = 48335043557059826411988191031702743391733063101 ∧ blockLinearRadius (-12033) (1) radius = 201330688653202031287145330034415492877 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-12033) (2) center = -48330983815040026129809831945580629000041556643 ∧ blockLinearRadius (-12033) (2) radius = 201313778404002543464256100670384341345 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache4352
