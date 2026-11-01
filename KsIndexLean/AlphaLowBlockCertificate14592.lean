module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache14592

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache14592
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-1793 : ℤ)+i.val) : ℝ) *
        sample (2*((-1793 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-1793) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-1793) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 14592 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+14592 = -1793 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+14592 = -1793 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-1793) (-2) center = -591112484084874968554657756520714118340001558463 ∧ blockLinearRadius (-1793) (-2) radius = 4155779786746598494346991587466038663058 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-1793) (-1) center = 590755687146621120171558415624460322611818769505 ∧ blockLinearRadius (-1793) (-1) radius = 4153269741480685557852337175622987174840 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-1793) (1) center = 590043386439963502781534610556871096946527833962 ∧ blockLinearRadius (-1793) (1) radius = 4148258754123144283430043220657047248032 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-1793) (2) center = -589687881107122346918172240383092366479402785553 ∧ blockLinearRadius (-1793) (2) radius = 4145757801011793343216302820253484190360 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache14592
