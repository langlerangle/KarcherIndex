module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache6144

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache6144
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-10241 : ℤ)+i.val) : ℝ) *
        sample (2*((-10241 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-10241) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-10241) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 6144 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6144 = -10241 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6144 = -10241 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-10241) (-2) center = -59860457785631911894654268782914279370520727017 ∧ blockLinearRadius (-10241) (-2) radius = 258633943782817850345005476882204128213 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-10241) (-1) center = 59854537311640370343465125883898085909991751522 ∧ blockLinearRadius (-10241) (-1) radius = 258608363388358612509647094385653143769 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-10241) (1) center = 59842699876522287885049435830806378658604068613 ∧ blockLinearRadius (-10241) (1) radius = 258557217777542918035618733757133424613 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-10241) (2) center = -59836782914701001989355700575615447185669191616 ∧ blockLinearRadius (-10241) (2) radius = 258531652558184627065528841345301401626 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache6144
