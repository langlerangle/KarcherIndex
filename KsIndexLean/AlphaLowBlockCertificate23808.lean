module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23808

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache23808
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((7423 : ℤ)+i.val) : ℝ) *
        sample (2*((7423 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (7423) n center : ℝ)/10^51| ≤
      (blockLinearRadius (7423) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 23808 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23808 = 7423 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23808 = 7423 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (7423) (-2) center = 263606591638183716888632952119480489074870210392 ∧ blockLinearRadius (7423) (-2) radius = 404752316207656079823939193963116148508 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (7423) (-1) center = -263641505455022717452915062965180710677504032001 ∧ blockLinearRadius (7423) (-1) radius = 404805924600188122335143837800587176698 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (7423) (1) center = -263711360844025323333775817479315102019606849211 ∧ blockLinearRadius (7423) (1) radius = 404913184002376939936157387835466604605 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (7423) (2) center = 263746302423545461789352432252144416341562404455 ∧ blockLinearRadius (7423) (2) radius = 404966835023329421778435736926764457072 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache23808
