module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache4608

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache4608
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-11777 : ℤ)+i.val) : ℝ) *
        sample (2*((-11777 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-11777) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-11777) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 4608 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4608 = -11777 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4608 = -11777 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-11777) (-2) center = -49745511863550253452011751314439715672445744094 ∧ blockLinearRadius (-11777) (-2) radius = 208207636319452639082979130456199340389 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-11777) (-1) center = 49741240732036052911363401198370183045962060247 ∧ blockLinearRadius (-11777) (-1) radius = 208189759527785875492423816441250196520 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-11777) (1) center = 49732700669025176752710073064953946253417080868 ∧ blockLinearRadius (-11777) (1) radius = 208154015152692964793595267150134146547 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-11777) (2) center = -49728431737150782621699717244680026002379171986 ∧ blockLinearRadius (-11777) (2) radius = 208136147567685851164317523485694571358 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache4608
