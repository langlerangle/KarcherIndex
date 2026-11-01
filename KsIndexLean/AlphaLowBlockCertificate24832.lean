module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache24832

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache24832
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((8447 : ℤ)+i.val) : ℝ) *
        sample (2*((8447 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (8447) n center : ℝ)/10^51| ≤
      (blockLinearRadius (8447) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 24832 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+24832 = 8447 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+24832 = 8447 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (8447) (-2) center = 218455868320098376747470419843350564532454709517 ∧ blockLinearRadius (8447) (-2) radius = 332992925441007210259603261219773210771 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (8447) (-1) center = -218481345938597468366928892747876621246601491163 ∧ blockLinearRadius (8447) (-1) radius = 333031761215333708095776631032683916206 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (8447) (1) center = -218532319009185405572803718861747566634930163147 ∧ blockLinearRadius (8447) (1) radius = 333109459948011507433518567595796885006 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (8447) (2) center = 218557814465436043378503778542063584100111252205 ∧ blockLinearRadius (8447) (2) radius = 333148322912706722060621864007989702589 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache24832
