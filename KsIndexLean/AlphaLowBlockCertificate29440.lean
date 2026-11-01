module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache29440

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache29440
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((13055 : ℤ)+i.val) : ℝ) *
        sample (2*((13055 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (13055) n center : ℝ)/10^51| ≤
      (blockLinearRadius (13055) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 29440 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+29440 = 13055 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+29440 = 13055 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (13055) (-2) center = 115784180941424292293127288847318591615312026305 ∧ blockLinearRadius (13055) (-2) radius = 172186610798987136398455281507490445188 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (13055) (-1) center = -115792963798402254739098813349984831729077927608 ∧ blockLinearRadius (13055) (-1) radius = 172199672109229427423294680815609405432 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (13055) (1) center = -115810533510453883268469064429765806968451362445 ∧ blockLinearRadius (13055) (1) radius = 172225800675440195178005940914375019406 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (13055) (2) center = 115819320366134279964287766607734741183658595376 ∧ blockLinearRadius (13055) (2) radius = 172238867932310966619018273725122954132 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache29440
