module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache4864

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache4864
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-11521 : ℤ)+i.val) : ℝ) *
        sample (2*((-11521 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-11521) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-11521) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 4864 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+4864 = -11521 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+4864 = -11521 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-11521) (-2) center = -51215907577838617621170315061571822582309643685 ∧ blockLinearRadius (-11521) (-2) radius = 215425159998684055219711676535755166429 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-11521) (-1) center = 51211411362295120819248054614816060883225230952 ∧ blockLinearRadius (-11521) (-1) radius = 215406247768316350369459599683961470359 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-11521) (1) center = 51202421299213298066786894191323177522323830339 ∧ blockLinearRadius (-11521) (1) radius = 215368433268108642799901988586130214487 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-11521) (2) center = -51197927451259274952977525121793901754177203046 ∧ blockLinearRadius (-11521) (2) radius = 215349530996520078886240310308916090749 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache4864
