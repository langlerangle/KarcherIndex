module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10496

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache10496
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-5889 : ℤ)+i.val) : ℝ) *
        sample (2*((-5889 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-5889) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-5889) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 10496 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+10496 = -5889 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+10496 = -5889 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-5889) (-2) center = -124194126706634689592509805798609857935816902534 ∧ blockLinearRadius (-5889) (-2) radius = 613594172954456626505184955520733471543 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-5889) (-1) center = 124172557110059008535800944001362479414855382236 ∧ blockLinearRadius (-5889) (-1) radius = 613487601704722382998206880186642018407 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-5889) (1) center = 124129440389587169873358155837551959164457754265 ∧ blockLinearRadius (-5889) (1) radius = 613274570243029072712447750782677642141 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-5889) (2) center = -124107893257886559942146295270017098324517057784 ∧ blockLinearRadius (-5889) (2) radius = 613168109992506530186534027634374602761 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache10496
