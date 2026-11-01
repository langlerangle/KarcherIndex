module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache23296

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache23296
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((6911 : ℤ)+i.val) : ℝ) *
        sample (2*((6911 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (6911) n center : ℝ)/10^51| ≤
      (blockLinearRadius (6911) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 23296 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+23296 = 6911 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+23296 = 6911 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (6911) (-2) center = 292427870202575623007459021896655271653706696062 ∧ blockLinearRadius (6911) (-2) radius = 450812227391277768509753140624921710718 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (6911) (-1) center = -292469419596796985450069942701700903469926003070 ∧ blockLinearRadius (6911) (-1) radius = 450876281111307735406059382611580014986 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (6911) (1) center = -292552553820301776315754184978313071039880465240 ∧ blockLinearRadius (6911) (1) radius = 451004443179404584318702947211699440442 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (6911) (2) center = 292594138659661248999446028505165764820586296681 ∧ blockLinearRadius (6911) (2) radius = 451068551543005176511068711510898672928 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache23296
