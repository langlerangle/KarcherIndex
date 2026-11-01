module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache26624

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache26624
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((10239 : ℤ)+i.val) : ℝ) *
        sample (2*((10239 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (10239) n center : ℝ)/10^51| ≤
      (blockLinearRadius (10239) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 26624 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26624 = 10239 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26624 = 10239 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (10239) (-2) center = 165066926697412473310473752361232707966861185628 ∧ blockLinearRadius (10239) (-2) radius = 248888922532233476699062832495664310883 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (10239) (-1) center = -165082849507546036284034073149670689004926209476 ∧ blockLinearRadius (10239) (-1) radius = 248912931112822198781295565551639478827 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (10239) (1) center = -165114704345808536659930062863975725959835095602 ∧ blockLinearRadius (10239) (1) radius = 248960962173030546622551656250731484854 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (10239) (2) center = 165130636375716556124307435508319997738639362633 ∧ blockLinearRadius (10239) (2) radius = 248984984655332706669493995404533721504 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache26624
