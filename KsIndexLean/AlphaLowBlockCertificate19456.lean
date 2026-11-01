module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache19456

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache19456
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((3071 : ℤ)+i.val) : ℝ) *
        sample (2*((3071 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (3071) n center : ℝ)/10^51| ≤
      (blockLinearRadius (3071) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 19456 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+19456 = 3071 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+19456 = 3071 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (3071) (-2) center = 939528500130250565463533976970944500819507045166 ∧ blockLinearRadius (3071) (-2) radius = 1514859531729821332247405322802564976026 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (3071) (-1) center = -939822491851108094580171130554149855779274346557 ∧ blockLinearRadius (3071) (-1) radius = 1515333566941382595772631357455501909731 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (3071) (1) center = -940411027898515189481001917653228692040412571454 ∧ blockLinearRadius (3071) (1) radius = 1516282528418350080238619610487783988529 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (3071) (2) center = 940705572571595891635912188118158516504014059312 ∧ blockLinearRadius (3071) (2) radius = 1516757455242540263311502344390230125077 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache19456
