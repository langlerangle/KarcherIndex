module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache15104

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache15104
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-1281 : ℤ)+i.val) : ℝ) *
        sample (2*((-1281 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-1281) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-1281) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 15104 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+15104 = -1281 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+15104 = -1281 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-1281) (-2) center = -921841669569491137545358879510842267733998205148 ∧ blockLinearRadius (-1281) (-2) radius = 7353239509169824189683240747508086747065 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-1281) (-1) center = 921034184890024149876740117928249212408454515475 ∧ blockLinearRadius (-1281) (-1) radius = 7346788949864344483749275008675716951125 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-1281) (1) center = 919423469475403612168465776603779639661639048457 ∧ blockLinearRadius (-1281) (1) radius = 7333921863486638693033874233111422575864 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-1281) (2) center = -918620231246185244909393029562391594931739884987 ∧ blockLinearRadius (-1281) (2) radius = 7327505276373947245990036398432679046863 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache15104
