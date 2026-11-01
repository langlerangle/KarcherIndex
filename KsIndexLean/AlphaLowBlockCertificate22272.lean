module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22272

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache22272
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((5887 : ℤ)+i.val) : ℝ) *
        sample (2*((5887 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (5887) n center : ℝ)/10^51| ≤
      (blockLinearRadius (5887) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 22272 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22272 = 5887 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22272 = 5887 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (5887) (-2) center = 368935364005357229866723032893531067160778962911 ∧ blockLinearRadius (5887) (-2) radius = 573887413608483552536678909047881700584 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (5887) (-1) center = -368996712641610473686231373649865402585749644855 ∧ blockLinearRadius (5887) (-1) radius = 573982843639595761950217849384892901847 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (5887) (1) center = -369119471152093309059731255734367482198288562449 ∧ blockLinearRadius (5887) (1) radius = 574173798960535858242987666784243904102 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (5887) (2) center = 369180881046705207316955887559862382684804045652 ∧ blockLinearRadius (5887) (2) radius = 574269324282069709052647323070138153236 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache22272
