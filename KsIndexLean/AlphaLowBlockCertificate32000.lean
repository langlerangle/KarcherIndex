module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache32000

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache32000
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((15615 : ℤ)+i.val) : ℝ) *
        sample (2*((15615 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (15615) n center : ℝ)/10^51| ≤
      (blockLinearRadius (15615) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 32000 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+32000 = 15615 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+32000 = 15615 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (15615) (-2) center = 89119690228058937505138759771630975654060024747 ∧ blockLinearRadius (15615) (-2) radius = 131186481821504006976089344875245633457 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (15615) (-1) center = -89125351086124767408963103059133686784574113631 ∧ blockLinearRadius (15615) (-1) radius = 131194814761103084307506953758874604940 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (15615) (1) center = -89136674960034926033400051674517355171966964358 ∧ blockLinearRadius (15615) (1) radius = 131211483816614882568636534755327738557 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (15615) (2) center = 89142337976153442072898428301319048626267329460 ∧ blockLinearRadius (15615) (2) radius = 131219819932931215837232399142336117692 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache32000
