module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache2048

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache2048
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-14337 : ℤ)+i.val) : ℝ) *
        sample (2*((-14337 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-14337) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-14337) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 2048 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+2048 = -14337 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+2048 = -14337 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-14337) (-2) center = -38314971325863209696463049826933938643321157568 ∧ blockLinearRadius (-14337) (-2) radius = 153541432019310507331287543015032817719 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-14337) (-1) center = 38312274438673580876778694006987272053796586350 ∧ blockLinearRadius (-14337) (-1) radius = 153530624590211747635807007685220796862 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-14337) (1) center = 38306881803124375575602373764452219770714405535 ∧ blockLinearRadius (-14337) (1) radius = 153509014295756033751057455570326575110 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-14337) (2) center = -38304186054604505936999602804103148481994565539 ∧ blockLinearRadius (-14337) (2) radius = 153498211429756717827797756347312923525 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache2048
