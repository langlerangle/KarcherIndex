module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache10240

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache10240
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-6145 : ℤ)+i.val) : ℝ) *
        sample (2*((-6145 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-6145) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-6145) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 10240 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+10240 = -6145 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+10240 = -6145 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-6145) (-2) center = -117433870478042727462128893275745086631221099167 ∧ blockLinearRadius (-6145) (-2) radius = 573944269501230276187402615826908015840 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-6145) (-1) center = 117414343479495255203731463996740812541819826898 ∧ blockLinearRadius (-6145) (-1) radius = 573848830014309750924310493650029888468 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-6145) (1) center = 117375308960651225165925798270952112196824212102 ∧ blockLinearRadius (-6145) (1) radius = 573658046245259141277409665444551825915 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-6145) (2) center = -117355801433878226244472646526452047063063422597 ∧ blockLinearRadius (-6145) (2) radius = 573562701931472658544147999284179564127 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache10240
