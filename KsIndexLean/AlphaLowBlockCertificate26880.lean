module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache26880

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache26880
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((10495 : ℤ)+i.val) : ℝ) *
        sample (2*((10495 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (10495) n center : ℝ)/10^51| ≤
      (blockLinearRadius (10495) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 26880 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+26880 = 10495 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+26880 = 10495 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (10495) (-2) center = 159228625833406787303606766161437826332759274600 ∧ blockLinearRadius (10495) (-2) radius = 239749987350973042840246846876207330514 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (10495) (-1) center = -159243615263497156693015484150795028050001865888 ∧ blockLinearRadius (10495) (-1) radius = 239772556946337733353350614465512859349 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (10495) (1) center = -159273602592112576074040328691655390427590041429 ∧ blockLinearRadius (10495) (1) radius = 239817708888030549636950170301996076358 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (10495) (2) center = 159288600492232630251711367909696490482519810763 ∧ blockLinearRadius (10495) (2) radius = 239840291236760287666431447431921507009 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache26880
