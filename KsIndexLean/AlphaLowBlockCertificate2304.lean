module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache2304

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache2304
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-14081 : ℤ)+i.val) : ℝ) *
        sample (2*((-14081 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-14081) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-14081) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 2304 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2304 = -14081 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2304 = -14081 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-14081) (-2) center = -39243392756504229931776503445824445035208211187 ∧ blockLinearRadius (-14081) (-2) radius = 157880442254457452259327843913785755707 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-14081) (-1) center = 39240579830518457507187383784281166983690616575 ∧ blockLinearRadius (-14081) (-1) radius = 157869125478287350114049137980881617559 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-14081) (1) center = 39234955188173265303387606985813623264594920693 ∧ blockLinearRadius (-14081) (1) radius = 157846496792464698847318953507694353580 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-14081) (2) center = -39232143471640463538195545844007454821052338008 ∧ blockLinearRadius (-14081) (2) radius = 157835184882114602428176713038248806653 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache2304
