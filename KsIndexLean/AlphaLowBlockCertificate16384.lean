module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache16384

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache16384
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-1 : ℤ)+i.val) : ℝ) *
        sample (2*((-1 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-1) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-1) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 16384 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+16384 = -1 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+16384 = -1 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-1) (-2) center = 1113936276892723633365242718378353691771579162096736 ∧ blockLinearRadius (-1) (-2) radius = 3964724878268744586572288190924307098173629 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-1) (-1) center = -1476622791332450479500476838661911352373516832802150 ∧ blockLinearRadius (-1) (-1) radius = 5353959825288333408784875577630795918966141 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-1) (1) center = -326581545579407164192077757145223336408736201007011 ∧ blockLinearRadius (-1) (1) radius = 16917452963600087466870801966692043558726323 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-1) (2) center = 134308136028919035207801608424218068406639063140454 ∧ blockLinearRadius (-1) (2) radius = 17664159405121424714704942719332519961290832 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache16384
