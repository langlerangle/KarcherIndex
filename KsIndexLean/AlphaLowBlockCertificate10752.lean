module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10752

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache10752
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-5633 : ℤ)+i.val) : ℝ) *
        sample (2*((-5633 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-5633) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-5633) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 10752 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+10752 = -5633 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+10752 = -5633 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-5633) (-2) center = -131667492231537428240191947859984605368348226151 ∧ blockLinearRadius (-5633) (-2) radius = 657984951679782432434297930747630827810 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-5633) (-1) center = 131643560231176627352265105064320450024591045363 ∧ blockLinearRadius (-5633) (-1) radius = 657865350317270428174178904732134564680 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-5633) (1) center = 131595722325081771014248679044547170679960063714 ∧ blockLinearRadius (-5633) (1) radius = 657626278007362387313005094708866344977 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-5633) (2) center = -131571816409863504807796638960251869728980263488 ∧ blockLinearRadius (-5633) (2) radius = 657506807012564233302353127486862748269 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache10752
