module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15616

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache15616
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-769 : ℤ)+i.val) : ℝ) *
        sample (2*((-769 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-769) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-769) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 15616 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15616 = -769 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15616 = -769 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-769) (-2) center = -1834447383213263507210508549804484161674678951317 ∧ blockLinearRadius (-769) (-2) radius = 18540831311519088654916323947771541790510 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-769) (-1) center = 1831497283950122210914232547905400277730907418774 ∧ blockLinearRadius (-769) (-1) radius = 18510839990758911926664824059093627792834 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-769) (1) center = 1825625843794608987619505401277367882365382596277 ∧ blockLinearRadius (-769) (1) radius = 18451151385524351865454409658796954575130 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-769) (2) center = -1822704408379279245052270429924546098470524433129 ∧ blockLinearRadius (-769) (2) radius = 18421453129282555036666744815449791675732 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache15616
