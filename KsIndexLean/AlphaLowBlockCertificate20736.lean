module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20736

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache20736
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((4351 : ℤ)+i.val) : ℝ) *
        sample (2*((4351 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (4351) n center : ℝ)/10^51| ≤
      (blockLinearRadius (4351) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 20736 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20736 = 4351 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20736 = 4351 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (4351) (-2) center = 570687015717114370526345654310702611433253982727 ∧ blockLinearRadius (4351) (-2) radius = 902751615483345667860880502341976107549 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (4351) (-1) center = -570814487224945417541886792837267335600710648840 ∧ blockLinearRadius (4351) (-1) radius = 902953261719913524758324322855360069940 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (4351) (1) center = -571069601199564157689547671240664492882041567364 ∧ blockLinearRadius (4351) (1) radius = 903356824635941306562777907340995272582 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (4351) (2) center = 571197243742817204390297096256736505460736588063 ∧ blockLinearRadius (4351) (2) radius = 903558741436364948841980015897223108842 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache20736
