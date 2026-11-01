module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache30208

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache30208
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((13823 : ℤ)+i.val) : ℝ) *
        sample (2*((13823 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (13823) n center : ℝ)/10^51| ≤
      (blockLinearRadius (13823) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 30208 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30208 = 13823 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30208 = 13823 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (13823) (-2) center = 106505937153008533354475648442603657947089208681 ∧ blockLinearRadius (13823) (-2) radius = 157873635284717122917375358584235922191 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (13823) (-1) center = -106513571422887720281536080485078874337184982450 ∧ blockLinearRadius (13823) (-1) radius = 157884951572954154841145256623858103409 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (13823) (1) center = -106528843246523245257280378134282329588269730971 ∧ blockLinearRadius (13823) (1) radius = 157907589017131476108179938978888672172 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (13823) (2) center = 106536480800750482954043202206323719553096857016 ∧ blockLinearRadius (13823) (2) radius = 157918910173769782869626223275937926285 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache30208
