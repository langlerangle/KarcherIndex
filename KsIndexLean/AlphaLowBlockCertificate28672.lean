module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache28672

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache28672
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((12287 : ℤ)+i.val) : ℝ) *
        sample (2*((12287 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (12287) n center : ℝ)/10^51| ≤
      (blockLinearRadius (12287) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 28672 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28672 = 12287 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28672 = 12287 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (12287) (-2) center = 126505305050192399505765376334950273302667670541 ∧ blockLinearRadius (12287) (-2) radius = 188780665346943743319861577342183772525 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (12287) (-1) center = -126515494837598719032333582293806081280969770743 ∧ blockLinearRadius (12287) (-1) radius = 188795871339786548811702971825546188682 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (12287) (1) center = -126535879337999765879680478601679714198274994674 ∧ blockLinearRadius (12287) (1) radius = 188826290675833027030650005708845019313 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (12287) (2) center = 126546074051788236808554823879456760291374389907 ∧ blockLinearRadius (12287) (2) radius = 188841504020221190493288444829696205244 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache28672
