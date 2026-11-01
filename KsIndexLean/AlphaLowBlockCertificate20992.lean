module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache20992

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache20992
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((4607 : ℤ)+i.val) : ℝ) *
        sample (2*((4607 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (4607) n center : ℝ)/10^51| ≤
      (blockLinearRadius (4607) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 20992 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+20992 = 4607 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+20992 = 4607 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (4607) (-2) center = 525618675440273506133132927861736483217847210618 ∧ blockLinearRadius (4607) (-2) radius = 828835214346137605193947335404430552589 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (4607) (-1) center = -525729726157709914983175677228635485109948582907 ∧ blockLinearRadius (4607) (-1) radius = 829010329927045058914466544842460365345 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (4607) (1) center = -525951968460663939348366497859507934372601952804 ∧ blockLinearRadius (4607) (1) radius = 829360783226438270692928472880849661894 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (4607) (2) center = 526063160105772494446565440280218919389564417377 ∧ blockLinearRadius (4607) (2) radius = 829536121038895424472626706775283533514 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache20992
