module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache5632

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache5632
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-10753 : ℤ)+i.val) : ℝ) *
        sample (2*((-10753 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-10753) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-10753) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 5632 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5632 = -10753 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5632 = -10753 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-10753) (-2) center = -56116922728735790522234551632752493463191552793 ∧ blockLinearRadius (-10753) (-2) radius = 239763520651769205878102892653282166362 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-10753) (-1) center = 56111640048893665086588439455364383841098954908 ∧ blockLinearRadius (-10753) (-1) radius = 239740949782345082681152718659992782751 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-10753) (1) center = 56101077672566460204271599432376716401916615008 ∧ blockLinearRadius (-10753) (1) radius = 239695820790378866298557335765149324217 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-10753) (2) center = -56095797975519796346004532730980728957431808299 ∧ blockLinearRadius (-10753) (2) radius = 239673262665437285491869233548811273031 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache5632
