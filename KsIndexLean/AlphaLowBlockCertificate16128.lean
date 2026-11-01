module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16128

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache16128
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-257 : ℤ)+i.val) : ℝ) *
        sample (2*((-257 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-257) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-257) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 16128 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16128 = -257 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16128 = -257 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-257) (-2) center = 39210950986984049390386864419033718213746990579396 ∧ blockLinearRadius (-257) (-2) radius = 13463279338109724388128814291043915581285663 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-257) (-1) center = -287717516109902807296565405457588435013185830286749 ∧ blockLinearRadius (-257) (-1) radius = 10218692333315751868358669089843859205979360 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-257) (1) center = -96620808461405080634353728579922041456395854298792 ∧ blockLinearRadius (-257) (1) radius = 3337405840435336338621884857563501401741849 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-257) (2) center = 76278021443642806245395161098417822839096742217351 ∧ blockLinearRadius (-257) (2) radius = 2678662526964894704368210932120727992629819 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache16128
