module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache9472

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache9472
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-6913 : ℤ)+i.val) : ℝ) *
        sample (2*((-6913 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-6913) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-6913) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 9472 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+9472 = -6913 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+9472 = -6913 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-6913) (-2) center = -100569523244804338793898230034167293238921006731 ∧ blockLinearRadius (-6913) (-2) radius = 477236341513040074470029584985940649976 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-6913) (-1) center = 100554694694022736152076015840874312236573609324 ∧ blockLinearRadius (-6913) (-1) radius = 477165973005477523223918276450846354753 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-6913) (1) center = 100525050708590241714277573000779151253782355573 ∧ blockLinearRadius (-6913) (1) radius = 477025298234407219103239846713274652177 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-6913) (2) center = -100510235270072307181933156131580438452488091931 ∧ blockLinearRadius (-6913) (2) radius = 476954991952547457171834397864055376916 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache9472
