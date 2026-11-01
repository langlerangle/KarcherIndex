module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache5888

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache5888
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-10497 : ℤ)+i.val) : ℝ) *
        sample (2*((-10497 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-10497) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-10497) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 5888 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+5888 = -10497 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+5888 = -10497 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-10497) (-2) center = -57935941217339331434403853546306911741844171314 ∧ blockLinearRadius (-10497) (-2) radius = 248903314655282442673665449488406387247 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-10497) (-1) center = 57930352604923221083047124488072248799315487019 ∧ blockLinearRadius (-10497) (-1) radius = 248879304686316138964181740124090550033 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-10497) (1) center = 57919178614161217899534293640244100216803400764 ∧ blockLinearRadius (-10497) (1) radius = 248831298642855443022937114563769436185 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-10497) (2) center = -57913593235191512946548820252972637584128412055 ∧ blockLinearRadius (-10497) (2) radius = 248807302565680948310995932937910171359 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache5888
