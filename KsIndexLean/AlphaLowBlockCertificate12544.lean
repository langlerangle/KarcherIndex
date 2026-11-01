module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12544

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache12544
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-3841 : ℤ)+i.val) : ℝ) *
        sample (2*((-3841 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-3841) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-3841) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 12544 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12544 = -3841 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12544 = -3841 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-3841) (-2) center = -217641234903888584422622234582540726103344124395 ∧ blockLinearRadius (-3841) (-2) radius = 1205706976609547007330689564062098685899 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-3841) (-1) center = 217582550395449480017871385814159845108105905750 ∧ blockLinearRadius (-3841) (-1) radius = 1205381836311565991895803728963285869190 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-3841) (1) center = 217465276306690787051920442360193641466716405133 ∧ blockLinearRadius (-3841) (1) radius = 1204732081719410484868204653610705441950 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-3841) (2) center = -217406686675179477364423459405840916749542095839 ∧ blockLinearRadius (-3841) (2) radius = 1204407467141548390682043612669736875029 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache12544
