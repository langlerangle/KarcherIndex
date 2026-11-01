module

public import KsIndexLean.AlphaLowModeBlock
public import KsIndexLean.AlphaLowProdValid
public import KsIndexLean.AlphaLowSampleCache6912

@[expose] public section


namespace KsIndex.AlphaRemarkTrial.Cache6912
def center (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).1
def radius (i : Fin 256) : ℤ := (entries[i.val]?.getD (0,0)).2

theorem actual_bound (n : ℤ) :
    |(∑ i : Fin 256, (rationalKernelWeight n ((-9473 : ℤ)+i.val) : ℝ) *
        sample (2*((-9473 : ℤ)+i.val)+1)) -
      (blockLinearNumerator (-9473) n center : ℝ)/10^51| ≤
      (blockLinearRadius (-9473) n radius : ℝ)/10^51 := by
  apply actual_cached_block_bound KsIndex.PositiveEnergyAlphaLowProd.valid
  · intro i
    convert low_block_covered 6912 256 (by norm_num) i using 1
    norm_num
  · intro i
    simpa only [center, mode, show (-16385 : ℤ)+6912 = -9473 by norm_num] using (checked i).1
  · intro i
    simpa only [radius, mode, show (-16385 : ℤ)+6912 = -9473 by norm_num] using (checked i).2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem sum_m2 : blockLinearNumerator (-9473) (-2) center = -66361977769251643160460643707781423375757415967 ∧ blockLinearRadius (-9473) (-2) radius = 291951905320902027525342459567168026097 := by decide +kernel
theorem sum_m1 : blockLinearNumerator (-9473) (-1) center = 66354874650394851996903376116348466938123231448 ∧ blockLinearRadius (-9473) (-1) radius = 291920655514778345088555665920865875661 := by decide +kernel
theorem sum_p1 : blockLinearNumerator (-9473) (1) center = 66340672973725542736779418499979218562035486081 ∧ blockLinearRadius (-9473) (1) radius = 291858175968899494925627306160079076449 := by decide +kernel
theorem sum_p2 : blockLinearNumerator (-9473) (2) center = -66333574414936824402612346532754912917971582948 ∧ blockLinearRadius (-9473) (2) radius = 291826946224849460852553145167055476438 := by decide +kernel
#print axioms actual_bound
end KsIndex.AlphaRemarkTrial.Cache6912
