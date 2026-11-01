module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache8704

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache8704
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-7681 : ℤ)+i.val) : ℝ) *
        sample (2*((-7681 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-7681) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-7681) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 8704 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+8704 = -7681 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+8704 = -7681 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-7681) (-2) center = -87532000053712425153870725133731203867233649161 ∧ blockLinearRadius (-7681) (-2) radius = 404784336637048226900763407027140958359 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-7681) (-1) center = 87520406932356373810703450761175467037795907349 ∧ blockLinearRadius (-7681) (-1) radius = 404730724003091941800112698417335286056 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-7681) (1) center = 87497229900748699432248333186641869103253553298 ∧ blockLinearRadius (-7681) (1) radius = 404623541333097994450310729222490974415 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-7681) (2) center = -87485645988057660681582765303324125412012277872 ∧ blockLinearRadius (-7681) (2) radius = 404569971285778688021007993113354655748 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache8704
