module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9216

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache9216
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-7169 : ℤ)+i.val) : ℝ) *
        sample (2*((-7169 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-7169) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-7169) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 9216 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9216 = -7169 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9216 = -7169 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-7169) (-2) center = -95865129489742377150528148648541475900510084711 ∧ blockLinearRadius (-7169) (-2) radius = 450850456682414324953746155377900636818 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-7169) (-1) center = 95851508841097741241219064628008063958837670483 ∧ blockLinearRadius (-7169) (-1) radius = 450786397529978141970115529620510138883 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-7169) (1) center = 95824279153230722532582442644369928143778366579 ∧ blockLinearRadius (-7169) (1) radius = 450658333826728226741803224451094986467 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-7169) (2) center = -95810670110710053910637638383856076015925102677 ∧ blockLinearRadius (-7169) (2) radius = 450594329260401531197369909339098698087 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache9216
