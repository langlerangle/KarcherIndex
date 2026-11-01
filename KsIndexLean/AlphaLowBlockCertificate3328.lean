module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache3328

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache3328
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-13057 : ℤ)+i.val) : ℝ) *
        sample (2*((-13057 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-13057) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-13057) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 3328 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3328 = -13057 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3328 = -13057 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-13057) (-2) center = -43382409032258664848618349401771192434186652676 ∧ blockLinearRadius (-13057) (-2) radius = 177449034248308917685417464078983438529 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-13057) (-1) center = 43379053084714146248518807908126622597453128649 ∧ blockLinearRadius (-13057) (-1) radius = 177435307165849021571267534723545324112 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-13057) (1) center = 43372342747077981101503143954050051700861892522 ∧ blockLinearRadius (-13057) (1) radius = 177407859371540347816349993420962018024 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-13057) (2) center = -43368988356745413917693407706982270694746692689 ∧ blockLinearRadius (-13057) (2) radius = 177394138658706100452067350916702364099 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache3328
