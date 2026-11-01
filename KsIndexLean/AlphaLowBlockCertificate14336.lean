module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14336

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache14336
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-2049 : ℤ)+i.val) : ℝ) *
        sample (2*((-2049 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-2049) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-2049) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 14336 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14336 = -2049 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14336 = -2049 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-2049) (-2) center = -495999644855917609566989455960537686709861876765 ∧ blockLinearRadius (-2049) (-2) radius = 3330870844192384554960400335196504052788 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-2049) (-1) center = 495740456127308667766494399239145986102517755572 ∧ blockLinearRadius (-2049) (-1) radius = 3329129461733964338897898737599128326934 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-2049) (1) center = 495222891671740893070829784549676264970596472449 ∧ blockLinearRadius (-2049) (1) radius = 3325652161568772168492987263332723842279 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-2049) (2) center = -494964515093920633688249083020162233689849385345 ∧ blockLinearRadius (-2049) (2) radius = 3323916238140131850370335721554598112277 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache14336
