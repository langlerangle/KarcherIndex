module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8192

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache8192
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-8193 : ℤ)+i.val) : ℝ) *
        sample (2*((-8193 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-8193) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-8193) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 8192 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8192 = -8193 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8192 = -8193 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-8193) (-2) center = -80388591140919031292233264481548658599462136436 ∧ blockLinearRadius (-8193) (-2) radius = 366011427142660065645540396879315846019 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-8193) (-1) center = 80378620392649238093399622816623480036815161073 ∧ blockLinearRadius (-8193) (-1) radius = 365966029157366439570214205760013747786 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-8193) (1) center = 80358686315036264486608822730686132655273219987 ∧ blockLinearRadius (-8193) (1) radius = 365875266966690163099241228315795869305 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-8193) (2) center = -80348722983853092938752851886717119148475472286 ∧ blockLinearRadius (-8193) (2) radius = 365829902752929485777806437217158331422 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache8192
