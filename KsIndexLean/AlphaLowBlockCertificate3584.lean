module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache3584

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache3584
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-12801 : ℤ)+i.val) : ℝ) *
        sample (2*((-12801 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-12801) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-12801) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 3584 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+3584 = -12801 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+3584 = -12801 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-12801) (-2) center = -44537649095881021493795250640778558572681156233 ∧ blockLinearRadius (-12801) (-2) radius = 182974199267268340205122358659834285052 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-12801) (-1) center = 44534134168967284131512218258669426650276187313 ∧ blockLinearRadius (-12801) (-1) radius = 182959758771451417564628981458018524253 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-12801) (1) center = 44527105979329324193636994867461792444834912840 ∧ blockLinearRadius (-12801) (1) radius = 182930884616915912881344887319934622254 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-12801) (2) center = -44523592716342469097059760156642740683157987239 ∧ blockLinearRadius (-12801) (2) radius = 182916450957118332474453317591398192175 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache3584
