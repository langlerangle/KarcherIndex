module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache27904

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache27904
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((11519 : ℤ)+i.val) : ℝ) *
        sample (2*((11519 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (11519) n center : ℝ)/10^51| ≤
      (blockLinearRadius (11519) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 27904 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27904 = 11519 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27904 = 11519 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (11519) (-2) center = 139005479581894402237237030739470835610965377554 ∧ blockLinearRadius (11519) (-2) radius = 208196906130428356679558483198147774600 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (11519) (-1) center = -139017414620838192287319192848694113646108303734 ∧ blockLinearRadius (11519) (-1) radius = 208214782000760105217696854741272968386 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (11519) (1) center = -139041290848498726420747881125494905124736265598 ∧ blockLinearRadius (11519) (1) radius = 208250542952352752937983349814533361961 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (11519) (2) center = 139053232038271869199902727386325381904377312336 ∧ blockLinearRadius (11519) (2) radius = 208268428035195895255936714370921543360 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache27904
