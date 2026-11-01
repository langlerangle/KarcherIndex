module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11264

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache11264
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-5121 : ℤ)+i.val) : ℝ) *
        sample (2*((-5121 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-5121) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-5121) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 11264 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11264 = -5121 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11264 = -5121 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-5121) (-2) center = -149229855235432233398475394617530972753716428252 ∧ blockLinearRadius (-5121) (-2) radius = 764503986831460239216113498159582396941 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-5121) (-1) center = 149199946490567562216547704928186042812145468189 ∧ blockLinearRadius (-5121) (-1) radius = 764350755829697699380959477900026479316 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-5121) (1) center = 149140164960283115027047312649541433528382921505 ∧ blockLinearRadius (-5121) (1) radius = 764044478066980465818517510521751892567 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-5121) (2) center = -149110292160451661557333053698632688307142157845 ∧ blockLinearRadius (-5121) (2) radius = 763891431232182359012451374684904485423 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache11264
