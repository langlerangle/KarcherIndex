module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache27136

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache27136
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((10751 : ℤ)+i.val) : ℝ) *
        sample (2*((10751 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (10751) n center : ℝ)/10^51| ≤
      (blockLinearRadius (10751) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 27136 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+27136 = 10751 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+27136 = 10751 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (10751) (-2) center = 153728961013297509970187190496512156634257355502 ∧ blockLinearRadius (10751) (-2) radius = 231152947342886924225455063847656850726 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (10751) (-1) center = -153743092127639550503489280174696584987997392988 ∧ blockLinearRadius (10751) (-1) radius = 231174195501723429698971366150422977299 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (10751) (1) center = -153771362151900776655503595910735323123095274071 ∧ blockLinearRadius (10751) (1) radius = 231216703541196730256478435585478340464 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (10751) (2) center = 153785501063253664172444723985064438607046826088 ∧ blockLinearRadius (10751) (2) radius = 231237963423989313363484049067935235198 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache27136
