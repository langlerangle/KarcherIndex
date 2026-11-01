module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache30976

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache30976
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((14591 : ℤ)+i.val) : ℝ) *
        sample (2*((14591 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (14591) n center : ℝ)/10^51| ≤
      (blockLinearRadius (14591) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 30976 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+30976 = 14591 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+30976 = 14591 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (14591) (-2) center = 98411979441336256501086815408879370261927036782 ∧ blockLinearRadius (14591) (-2) radius = 145426880700872219020540076086229372662 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (14591) (-1) center = -98418665454819560061332345025922169621171421961 ∧ blockLinearRadius (14591) (-1) radius = 145436760875024272913892445729568865723 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (14591) (1) center = -98432040207672509550770591765288232330456382938 ∧ blockLinearRadius (14591) (1) radius = 145456525251479223716003999177941177478 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (14591) (2) center = 98438728947412637764458977099341461808941177222 ∧ blockLinearRadius (14591) (2) radius = 145466409454329597850139161517907883379 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache30976
