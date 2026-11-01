module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache21504

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache21504
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((5119 : ℤ)+i.val) : ℝ) *
        sample (2*((5119 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (5119) n center : ℝ)/10^51| ≤
      (blockLinearRadius (5119) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 21504 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+21504 = 5119 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+21504 = 5119 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (5119) (-2) center = 451535891637977307516305081725557360118845854494 ∧ blockLinearRadius (5119) (-2) radius = 707866039146905404030131259623888833640 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (5119) (-1) center = -451621973567957698616198655181238347177853911708 ∧ blockLinearRadius (5119) (-1) radius = 708000990020230293244455086015388301440 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (5119) (1) center = -451794235950272127933008005103148377373002767914 ∧ blockLinearRadius (5119) (1) radius = 708271046222383254698670444211153910029 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (5119) (2) center = 451880416440207681070241712087303365251071425659 ∧ blockLinearRadius (5119) (2) radius = 708406151610160654180052998144509048022 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache21504
