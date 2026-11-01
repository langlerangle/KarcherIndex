module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache1024

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache1024
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-15361 : ℤ)+i.val) : ℝ) *
        sample (2*((-15361 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-15361) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-15361) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 1024 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+1024 = -15361 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+1024 = -15361 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-15361) (-2) center = -34956813461133474338280065541262032201858615243 ∧ blockLinearRadius (-15361) (-2) radius = 138008863608947634831265885673273277585 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-15361) (-1) center = 34954518376988533944009815956987210495935996691 ∧ blockLinearRadius (-15361) (-1) radius = 137999802612994946084300330081259490141 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-15361) (1) center = 34949929112701578155304258409763385851538506305 ∧ blockLinearRadius (-15361) (1) radius = 137981684190112512123488403342364103511 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-15361) (2) center = -34947634932440876209020415792998631811512015351 ∧ blockLinearRadius (-15361) (2) radius = 137972626762714187504184381097112829164 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache1024
