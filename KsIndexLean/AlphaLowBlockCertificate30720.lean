module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache30720

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache30720
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((14335 : ℤ)+i.val) : ℝ) *
        sample (2*((14335 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (14335) n center : ℝ)/10^51| ≤
      (blockLinearRadius (14335) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 30720 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30720 = 14335 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30720 = 14335 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (14335) (-2) center = 100991824515860196237755258415916116550189896251 ∧ blockLinearRadius (14335) (-2) radius = 149389965093287633951753223575206996663 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (14335) (-1) center = -100998807255742682592475024479945682147507099417 ∧ blockLinearRadius (14335) (-1) radius = 149400294175262376091023478567177715545 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (14335) (1) center = -101012775632772260058763457004425144714373189686 ∧ blockLinearRadius (14335) (1) radius = 149420956624940537698498766098278334587 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (14335) (2) center = 101019761270320098445048346526462099345604899532 ∧ blockLinearRadius (14335) (2) radius = 149431289993236756548861592840313797459 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache30720
