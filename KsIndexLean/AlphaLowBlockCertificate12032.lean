module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12032

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache12032
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-4353 : ℤ)+i.val) : ℝ) *
        sample (2*((-4353 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-4353) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-4353) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 12032 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12032 = -4353 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12032 = -4353 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-4353) (-2) center = -184704760812337249972518357158269057255889390996 ∧ blockLinearRadius (-4353) (-2) radius = 988372788574390118611423020147838632946 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-4353) (-1) center = 184661002923794891344723841088452273002672157397 ∧ blockLinearRadius (-4353) (-1) radius = 988138616964807676526844094169621268665 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-4353) (1) center = 184573549335627033902724630986901932528065215311 ∧ blockLinearRadius (-4353) (1) radius = 987670606578378775875969941280596689688 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-4353) (2) center = -184529853606538450769738220244967833245454514407 ∧ blockLinearRadius (-4353) (2) radius = 987436767643834249831458672702557637069 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache12032
