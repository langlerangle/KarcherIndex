module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache22784

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache22784
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((6399 : ℤ)+i.val) : ℝ) *
        sample (2*((6399 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (6399) n center : ℝ)/10^51| ≤
      (blockLinearRadius (6399) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 22784 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+22784 = 6399 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+22784 = 6399 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (6399) (-2) center = 326961644885341972746210747128058527249495423058 ∧ blockLinearRadius (6399) (-2) radius = 506229920307501685727334864183967994173 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (6399) (-1) center = -327011746833277052777659579905070241959484400084 ∧ blockLinearRadius (6399) (-1) radius = 506307492986509234818463801870650609242 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (6399) (1) center = -327111996813392220784717856834565477327137449311 ∧ blockLinearRadius (6399) (1) radius = 506462709697129506825538257593252598289 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (6399) (2) center = 327162144859705862217927094613595347538577119047 ∧ blockLinearRadius (6399) (2) radius = 506540353750625483736894451500051292439 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache22784
