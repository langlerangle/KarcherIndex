module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache12288

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache12288
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-4097 : ℤ)+i.val) : ℝ) *
        sample (2*((-4097 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-4097) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-4097) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 12288 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+12288 = -4097 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+12288 = -4097 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-4097) (-2) center = -199987041025698666723400172802651487649498027779 ∧ blockLinearRadius (-4097) (-2) radius = 1088134496611831567164448929440987576926 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-4097) (-1) center = 199936601361428548176254693413108991560976185002 ∧ blockLinearRadius (-4097) (-1) radius = 1087860027625918285828120905372916460494 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-4097) (1) center = 199835798350590834140951680238143720789197081145 ∧ blockLinearRadius (-4097) (1) radius = 1087311504977779870264247760432638606354 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-4097) (2) center = -199785434965528801306940072375084657373753943316 ∧ blockLinearRadius (-4097) (2) radius = 1087037451106047192625873891100197931885 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache12288
