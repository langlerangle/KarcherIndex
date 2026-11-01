module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache11520

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache11520
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-4865 : ℤ)+i.val) : ℝ) *
        sample (2*((-4865 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-4865) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-4865) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 11520 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+11520 = -4865 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+11520 = -4865 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-4865) (-2) center = -159625147533711683875368020572734333839924675652 ∧ blockLinearRadius (-4865) (-2) radius = 828939271175633675786204701550032528973 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-4865) (-1) center = 159591424198018580223683545431328251898215119605 ∧ blockLinearRadius (-4865) (-1) radius = 828764133604394257900116598758102585572 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-4865) (1) center = 159524020266502969064888853637112477875126122179 ∧ blockLinearRadius (-4865) (1) radius = 828414080439627839884319187584795961863 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-4865) (2) center = -159490339652624173365745621870865593125261995035 ∧ blockLinearRadius (-4865) (2) radius = 828239164752316139793206751108704299296 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache11520
