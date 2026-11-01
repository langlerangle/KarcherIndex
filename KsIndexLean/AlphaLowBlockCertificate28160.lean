module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache28160

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache28160
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((11775 : ℤ)+i.val) : ℝ) *
        sample (2*((11775 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (11775) n center : ℝ)/10^51| ≤
      (blockLinearRadius (11775) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 28160 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+28160 = 11775 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+28160 = 11775 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (11775) (-2) center = 134616304027376341173178875118478005083848357892 ∧ blockLinearRadius (11775) (-2) radius = 201371278730465238320481719626567576357 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (11775) (-1) center = -134627613599726396236822395220778484704761556305 ∧ blockLinearRadius (11775) (-1) radius = 201388196652149972181442251987273574187 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (11775) (1) center = -134650238446537634493404771050048699536355548789 ∧ blockLinearRadius (11775) (1) radius = 201422041025292286436199295081632796407 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (11775) (2) center = 134661553721957240530123239036461113559315489713 ∧ blockLinearRadius (11775) (2) radius = 201438967478183572183753151446578638186 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache28160
