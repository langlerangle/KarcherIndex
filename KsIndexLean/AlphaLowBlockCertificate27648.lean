module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache27648

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache27648
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((11263 : ℤ)+i.val) : ℝ) *
        sample (2*((11263 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (11263) n center : ℝ)/10^51| ≤
      (blockLinearRadius (11263) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 27648 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27648 = 11263 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27648 = 11263 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (11263) (-2) center = 143640448082337563001105607747913887746460390624 ∧ blockLinearRadius (11263) (-2) radius = 215413811231681827317699225074050197144 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (11263) (-1) center = -143653058283822343263468975955186934847670393988 ∧ blockLinearRadius (11263) (-1) radius = 215432722465696906942178038986305708783 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (11263) (1) center = -143678285330539022132862351185569568563170807264 ∧ blockLinearRadius (11263) (1) radius = 215470554897228469817644840380488728896 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (11263) (2) center = 143690902176937836021531783728721285054380550063 ∧ blockLinearRadius (11263) (2) radius = 215489476096494957989373579835601548308 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache27648
